# Archivo: complete_encode.py

import sys
import time
from classes_ctt import parse_ctt, Instance
from utils import (hour_for_day, day, map_teacher, exactly, at_least,
                   is_first_slot_of_day, is_last_slot_of_day)
from pysat.formula import IDPool, WCNF
from pysat.card import CardEnc, ITotalizer
from pysat.examples.rc2 import RC2

#==============================================================================
# FUNCIONES SUAVES (WEIGHTED) - Se usan solo en modo MaxSAT
#==============================================================================

def room_stability_weighted(courses, rooms, cr, vpool):
    hard_clauses, weighted_soft_clauses = [], []
    WEIGHT = 1
    for c_id in courses:
        literals = [cr[(c_id, r_id)] for r_id in rooms if (c_id, r_id) in cr]
        if len(literals) > 1:
            tot = ITotalizer(lits=literals, ubound=len(literals))
            hard_clauses.extend(tot.cnf.clauses)
            if tot.top_id > vpool.top: vpool.top = tot.top_id
            for i in range(1, len(literals)):
                if i < len(tot.rhs):
                    weighted_soft_clauses.append((WEIGHT, [-tot.rhs[i]]))
    return hard_clauses, weighted_soft_clauses

def room_capacity_weighted(courses, rooms, chr_vars):
    weighted_soft_clauses = []
    for (c_id, h, r_id), lit_chr in chr_vars.items():
        if courses[c_id].num_students > rooms[r_id].capacity:
            cost = courses[c_id].num_students - rooms[r_id].capacity
            weighted_soft_clauses.append((cost, [-lit_chr]))
    return weighted_soft_clauses

def min_working_days_weighted(courses, cd, vpool, num_days):
    hard_clauses, weighted_soft_clauses = [], []
    WEIGHT = 5
    for c_id, course_obj in courses.items():
        literals = [cd[(c_id, d)] for d in range(num_days) if (c_id, d) in cd]
        k = course_obj.min_working_days
        if literals and k > 1:
            tot = ITotalizer(lits=literals, ubound=len(literals))
            hard_clauses.extend(tot.cnf.clauses)
            if tot.top_id > vpool.top: vpool.top = tot.top_id
            for i in range(2, k + 1):
                if (i - 1) < len(tot.rhs):
                    weighted_soft_clauses.append((WEIGHT, [tot.rhs[i - 1]]))
    return hard_clauses, weighted_soft_clauses

def isolated_lectures_weighted(kh, curricula, ppd, total_hours):
    weighted_clauses = []
    WEIGHT = 2
    for k_id in curricula:
        for h in range(total_hours):
            if (k_id, h) in kh:
                clause = [-kh[(k_id, h)]]
                if not is_first_slot_of_day(h, ppd) and (k_id, h - 1) in kh:
                    clause.append(kh[(k_id, h - 1)])
                if not is_last_slot_of_day(h, ppd) and (k_id, h + 1) in kh:
                    clause.append(kh[(k_id, h + 1)])
                if len(clause) > 1:
                    weighted_clauses.append((WEIGHT, clause))
    return weighted_clauses

#==============================================================================
# ENCODER PRINCIPAL - Con la lógica correcta
#==============================================================================

def encoder(instance: Instance, type_sat:int = 0):
    vpool = IDPool(start_from=1)
    hard_clauses = []
    soft_clauses_weighted = []
    
    courses, rooms, curricula = instance.courses, instance.rooms, instance.curricula
    ppd, days = instance.periods_per_day, instance.num_days
    total_hours = ppd * days

    ch = get_ch(courses, total_hours, vpool)
    cd = get_cd(courses, days, vpool)
    cr = get_cr(courses, rooms, vpool)
    kh = get_kh(curricula, total_hours, vpool)
    chr_vars = get_chr(courses, total_hours, rooms, vpool)

    # --- Restricciones Siempre Duras ---
    hard_clauses.extend(relation_ch_chr(ch, chr_vars, rooms))
    hard_clauses.extend(relation_cr_chr(cr, chr_vars, total_hours))
    hard_clauses.extend(relation_ch_cd(ch, cd, ppd))
    hard_clauses.extend(relation_ch_kh(ch, kh, curricula))
    hard_clauses.extend(curriculum_clashes(ch, curricula, total_hours))
    hard_clauses.extend(teacher_clashes(courses, ch, total_hours))
    hard_clauses.extend(room_clashes(chr_vars))
    hard_clauses.extend(time_slot_availability(ch, instance.unavailabilities, ppd))
    hard_clauses.extend(number_of_lectures(courses, ch, total_hours, vpool))

    if type_sat == 0:
        # MODO SAT: Añadir versiones duras de las 4 restricciones
        hard_clauses.extend(min_working_days(courses, cd, vpool, days))
        hard_clauses.extend(isolated_lectures(kh, curricula, ppd, total_hours))
        hard_clauses.extend(room_stability_hard_version(courses, rooms, cr, vpool))
        hard_clauses.extend(room_capacity(courses, rooms, chr_vars))
        return hard_clauses, None, vpool
    
    elif type_sat == 1:
        # MODO MAXSAT: Añadir versiones suaves de las 4 restricciones
        new_hard, new_soft = min_working_days_weighted(courses, cd, vpool, days)
        hard_clauses.extend(new_hard)
        soft_clauses_weighted.extend(new_soft)
        
        soft_clauses_weighted.extend(isolated_lectures_weighted(kh, curricula, ppd, total_hours))
        
        new_hard, new_soft = room_stability_weighted(courses, rooms, cr, vpool)
        hard_clauses.extend(new_hard)
        soft_clauses_weighted.extend(new_soft)
        
        soft_clauses_weighted.extend(room_capacity_weighted(courses, rooms, chr_vars))
        
        return hard_clauses, soft_clauses_weighted, vpool

#==============================================================================
# FUNCIONES AUXILIARES (Duras y de creación de variables)
#==============================================================================

# --- Versiones Duras ---
def room_stability_hard_version(courses, rooms, cr, vpool):
    clauses = []
    for c_id in courses:
        lits = [cr[(c_id, r_id)] for r_id in rooms if (c_id, r_id) in cr]
        if lits: clauses.extend(CardEnc.equals(lits=lits, bound=1, vpool=vpool).clauses)
    return clauses

def room_capacity(courses, rooms, chr_vars):
    return [[-lit_chr] for (c_id, h, r_id), lit_chr in chr_vars.items() if courses[c_id].num_students > rooms[r_id].capacity]

def isolated_lectures(kh, curricula, ppd, total_hours):
    clauses = []
    for k_id in curricula:
        for h in range(total_hours):
            if (k_id, h) in kh:
                clause = [-kh[(k_id, h)]]
                if not is_first_slot_of_day(h, ppd) and (k_id, h - 1) in kh: clause.append(kh[(k_id, h - 1)])
                if not is_last_slot_of_day(h, ppd) and (k_id, h + 1) in kh: clause.append(kh[(k_id, h + 1)])
                if len(clause) > 1: clauses.append(clause)
    return clauses

def min_working_days(courses, cd, vpool, num_days):
    clauses = []
    for c_id, course in courses.items():
        lits = [cd[(c_id, d)] for d in range(num_days) if (c_id, d) in cd]
        if lits and course.min_working_days > 0:
            clauses.extend(CardEnc.atleast(lits=lits, bound=course.min_working_days, vpool=vpool).clauses)
    return clauses

# --- Restricciones Siempre Duras ---
def room_clashes(chr_vars):
    clauses = []
    chr_by_hr = {}
    for (c, h, r), lit in chr_vars.items():
        chr_by_hr.setdefault((h, r), []).append(lit)
    for lits in chr_by_hr.values():
        if len(lits) > 1: clauses.extend(CardEnc.atmost(lits=lits, bound=1).clauses)
    return clauses

def relation_ch_chr(ch, chr_vars, rooms):
    clauses = []
    for (c, h), lit_ch in ch.items():
        lits = [chr_vars[(c, h, r)] for r in rooms if (c, h, r) in chr_vars]
        clauses.append([-lit_ch] + lits)
        for lit_chr in lits: clauses.append([-lit_chr, lit_ch])
    return clauses

def relation_cr_chr(cr, chr_vars, total_hours):
    clauses = []
    for (c, r), lit_cr in cr.items():
        lits = [chr_vars[(c, h, r)] for h in range(total_hours) if (c, h, r) in chr_vars]
        clauses.append([-lit_cr] + lits)
        for lit_chr in lits: clauses.append([-lit_chr, lit_cr])
    return clauses

def number_of_lectures(courses, ch, total_hours, vpool):
    clauses = []
    for c_id, course in courses.items():
        lits = [ch[(c_id, h)] for h in range(total_hours) if (c_id, h) in ch]
        clauses.extend(CardEnc.equals(lits=lits, bound=course.num_lectures, vpool=vpool).clauses)
    return clauses

def time_slot_availability(ch, unavailabilities, ppd):
    return [[-ch[(u.course_id, u.day * ppd + u.day_period)]] for u in unavailabilities]

def teacher_clashes(courses, ch, total_hours):
    clauses = []
    teacher_map = map_teacher(courses)
    for course_list in teacher_map.values():
        if len(course_list) > 1:
            for h in range(total_hours):
                lits = [ch[(c, h)] for c in course_list if (c, h) in ch]
                if len(lits) > 1: clauses.extend(CardEnc.atmost(lits=lits, bound=1).clauses)
    return clauses

def curriculum_clashes(ch, curricula, total_hours):
    clauses = []
    for curriculum in curricula.values():
        for h in range(total_hours):
            lits = [ch[(c, h)] for c in curriculum.courses if (c, h) in ch]
            if len(lits) > 1: clauses.extend(CardEnc.atmost(lits=lits, bound=1).clauses)
    return clauses

def relation_ch_kh(ch, kh, curricula):
    clauses = []
    for (c, h), lit_ch in ch.items():
        for k_id, curriculum in curricula.items():
            if c in curriculum.courses and (k_id, h) in kh:
                clauses.append([-lit_ch, kh[(k_id, h)]])
    return clauses

def relation_ch_cd(ch, cd, ppd):
    clauses = []
    for (c, h), lit_ch in ch.items(): clauses.append([-lit_ch, cd[(c, day(h, ppd))]])
    for (c, d), lit_cd in cd.items():
        lits = [ch[(c, h)] for h in hour_for_day(d, ppd) if (c, h) in ch]
        clauses.append([-lit_cd] + lits)
    return clauses

# --- Creación de Variables ---
def get_ch(courses, hours, vpool):
    return {(c, h): vpool.id(f'ch_{c}_{h}') for c in courses for h in range(hours)}
def get_cd(courses, days, vpool):
    return {(c, d): vpool.id(f'cd_{c}_{d}') for c in courses for d in range(days)}
def get_cr(courses, rooms, vpool):
    return {(c, r): vpool.id(f'cr_{c}_{r}') for c in courses for r in rooms}
def get_kh(curricula, hours, vpool):
    return {(k, h): vpool.id(f'kh_{k}_{h}') for k in curricula for h in range(hours)}
def get_chr(courses, hours, rooms, vpool):
    return {(c, h, r): vpool.id(f'chr_{c}_{h}_{r}') for c in courses for h in range(hours) for r in rooms}

#==============================================================================
# BLOQUE DE EJECUCIÓN PRINCIPAL
#==============================================================================
if __name__ == "__main__":
    input_file = sys.argv[1] if len(sys.argv) > 1 else "data/toy.txt"
    print(f"--- Running Encoder in MaxSAT mode on: {input_file} ---")

    instance = parse_ctt(input_file)
    
    print(f"Encoding '{instance.name}'...")
    start_time = time.time()
    hard_clauses, soft_clauses, vpool = encoder(instance, type_sat=1)
    encoding_time = time.time() - start_time
    
    soft_count = len(soft_clauses) if soft_clauses else 0
    print(f"Generated {len(hard_clauses)} hard and {soft_count} soft clauses in {encoding_time:.2f}s.")
    print(f"Total variables: {vpool.top}")

    print("Preparing WCNF formula...")
    wcnf = WCNF()
    wcnf.nv = vpool.top
    for clause in hard_clauses: wcnf.append(clause)
    if soft_clauses:
        for weight, clause in soft_clauses: wcnf.append(clause, weight=weight)
    
    print("Starting MaxSAT solver...")
    start_time = time.time()
    with RC2(wcnf) as solver:
        if solver.compute():
            solving_time = time.time() - start_time
            print(f"\nSolution found in {solving_time:.2f}s!")
            print(f"Optimal cost: {solver.cost}")
        else:
            solving_time = time.time() - start_time
            print(f"\nProblem is UNSATISFIABLE. Search terminated in {solving_time:.2f}s.")
            print("This indicates a contradiction in the HARD clauses.")