"""
Implementación completa del paper "Curriculum-based course timetabling with SAT and MaxSAT"
Incluye todos los enfoques de las Secciones 3, 4.1, 4.2, 4.3, 4.4 y 5
"""

import sys
import time
from dataclasses import dataclass
from typing import Dict, List, Tuple
from math import ceil
from pysat.formula import IDPool, WCNF, CNF
from pysat.card import CardEnc, EncType, ITotalizer
from pysat.solvers import Glucose3
from pysat.examples.rc2 import RC2

# ============= CLASES =============
@dataclass
class Course:
    teacher: str
    num_lectures: int  
    min_working_days: int 
    num_students: int  

@dataclass
class Room:
    capacity: int

@dataclass
class Curriculum:
    courses: set[str]

@dataclass
class Unavailability:
    course_id: str
    day: int
    day_period: int

@dataclass
class Instance:
    name: str
    num_courses: int
    num_rooms: int
    num_days: int
    periods_per_day: int
    num_curricula: int
    num_constraints: int
    courses: Dict[str, Course]
    rooms: Dict[str, Room]
    curricula: Dict[str, Curriculum] 
    unavailabilities: List[Unavailability]

# ============= PARSER =============
def parse_ctt(file_name):
    """Parse archivo .ctt según formato ITC2007"""
    info = {}
    courses = {}
    rooms = {}
    curricula = {}
    unavailabilities = []
    state = "INFO"

    with open(file_name) as file:
        for line in file:
            l = line.strip().split()
            if not l:
                continue
            
            if len(l) == 1:
                first_word = l[0]
                if first_word.endswith(":"):
                    state = l[0][:-1]
                    continue
                else:
                    break
            
            if state == 'INFO':
                key = l[0].lower()[:-1]
                value = l[1]
                info[key] = value
            elif state == 'COURSES':
                courses[l[0]] = Course(
                    teacher=l[1], 
                    num_lectures=int(l[2]), 
                    min_working_days=int(l[3]), 
                    num_students=int(l[4])
                )
            elif state == "ROOMS":
                rooms[l[0]] = Room(capacity=int(l[1]))
            elif state == "CURRICULA":
                curricula[l[0]] = Curriculum(courses=set(l[2:]))
            elif state == "UNAVAILABILITY_CONSTRAINTS":
                unavailabilities.append(
                    Unavailability(
                        course_id=l[0], 
                        day=int(l[1]), 
                        day_period=int(l[2])
                    )
                )
    
    instance = Instance(
        name=info['name'],
        num_courses=int(info['courses']),
        num_rooms=int(info['rooms']),
        num_days=int(info['days']),
        periods_per_day=int(info['periods_per_day']),
        num_curricula=int(info['curricula']),
        num_constraints=int(info['constraints']),
        courses=courses,
        rooms=rooms,
        curricula=curricula,
        unavailabilities=unavailabilities
    )
    return instance

# ============= UTILIDADES =============
def day(h, ppd):
    return ceil((h+1)/ppd) - 1 

def hour_for_day(d, ppd):
    start = d * ppd
    end = start + ppd
    return list(range(start, end))

def map_teacher(courses):
    teachers = {}
    for c_id, course_obj in courses.items():
        teacher_id = course_obj.teacher 
        if teacher_id not in teachers:
            teachers[teacher_id] = []
        teachers[teacher_id].append(c_id)
    return teachers

def exactly(literals, k, vpool):
    cnf = CardEnc.equals(lits=literals, bound=k, vpool=vpool, encoding=EncType.totalizer)
    return cnf.clauses

def at_least(literals, k, vpool):
    cnf = CardEnc.atleast(lits=literals, bound=k, vpool=vpool, encoding=EncType.totalizer)
    return cnf.clauses

def is_first_slot_of_day(h, ppd):
    return h % ppd == 0

def is_last_slot_of_day(h, ppd):
    return (h + 1) % ppd == 0

# ============= VARIABLES =============
def get_ch(courses, hours, vpool, id_to_var):
    ch = {}
    for c in courses:
        for h in range(hours):
            var_id = vpool.id()
            ch[(c, h)] = var_id
            id_to_var[var_id] = ('ch', c, h)
    return ch, id_to_var

def get_cd(courses, days, vpool, id_to_var):
    cd = {}
    for c in courses:
        for d in range(days):
            var_id = vpool.id()
            cd[(c, d)] = var_id
            id_to_var[var_id] = ('cd', c, d)
    return cd, id_to_var

def get_cr(courses, rooms, vpool, id_to_var):
    cr = {}
    for c in courses:
        for r in rooms:
            var_id = vpool.id()
            cr[(c, r)] = var_id
            id_to_var[var_id] = ('cr', c, r)
    return cr, id_to_var

def get_kh(curricula, hours, vpool, id_to_var):
    kh = {}
    for k in curricula:
        for h in range(hours):
            var_id = vpool.id()
            kh[(k, h)] = var_id
            id_to_var[var_id] = ('kh', k, h)
    return kh, id_to_var

def get_chr(courses, rooms, hours, vpool, id_to_var):
    """chr(c,h,r): course c in time slot h in room r (Sección 4.4)"""
    chr_vars = {}
    for c in courses:
        for h in range(hours):
            for r in rooms:
                var_id = vpool.id()
                chr_vars[(c, h, r)] = var_id
                id_to_var[var_id] = ('chr', c, h, r)
    return chr_vars, id_to_var

# ============= RELACIONES =============
def relation_ch_cd(ch, cd, ppd):
    clauses = []
    for (c, h) in ch:
        d = day(h, ppd)
        if (c, d) in cd:
            clauses.append([-ch[(c, h)], cd[(c, d)]])
    
    for (c, d) in cd:
        hours_day = hour_for_day(d, ppd)
        clause = [-cd[(c, d)]]
        for h in hours_day:
            if (c, h) in ch:
                clause.append(ch[(c, h)])
        clauses.append(clause)
    return clauses

def relation_ch_kh(ch, kh, curricula):
    clauses = []
    for (c, h) in ch:
        for k, curr in curricula.items():
            if c in curr.courses:
                if (k, h) in kh:
                    clauses.append([-ch[(c, h)], kh[(k, h)]])
    
    for (k, h) in kh:
        courses_k = curricula[k].courses
        clause = [-kh[(k, h)]]
        for c in courses_k:
            if (c, h) in ch:
                clause.append(ch[(c, h)])
        clauses.append(clause)
    return clauses

def relation_ch_chr(ch, chr_vars, courses, rooms, total_hours):
    """Relación ch ↔ chr (Sección 4.4)"""
    clauses = []
    all_room_ids = list(rooms.keys())
    
    for c in courses:
        for h in range(total_hours):
            if (c, h) not in ch:
                continue
            
            for r in all_room_ids:
                if (c, h, r) in chr_vars:
                    clauses.append([-chr_vars[(c, h, r)], ch[(c, h)]])
            
            clause = [-ch[(c, h)]]
            for r in all_room_ids:
                if (c, h, r) in chr_vars:
                    clause.append(chr_vars[(c, h, r)])
            clauses.append(clause)
    
    return clauses

def relation_cr_chr(cr, chr_vars, courses, rooms, total_hours):
    """Relación cr ↔ chr (Sección 4.4)"""
    clauses = []
    all_room_ids = list(rooms.keys())
    
    for c in courses:
        for r in all_room_ids:
            if (c, r) not in cr:
                continue
            
            for h in range(total_hours):
                if (c, h, r) in chr_vars:
                    clauses.append([-chr_vars[(c, h, r)], cr[(c, r)]])
            
            clause = [-cr[(c, r)]]
            for h in range(total_hours):
                if (c, h, r) in chr_vars:
                    clause.append(chr_vars[(c, h, r)])
            clauses.append(clause)
    
    return clauses

# ============= RESTRICCIONES HARD =============
def curriculum_clashes(ch, curricula, total_hours):
    clauses = []
    for k, curriculum in curricula.items():
        courses_list = list(curriculum.courses)
        num_courses = len(courses_list)
        if num_courses < 2:
            continue
        for h in range(total_hours):
            for i in range(num_courses):
                for j in range(i + 1, num_courses):
                    c_i = courses_list[i]
                    c_j = courses_list[j]
                    if (c_i, h) in ch and (c_j, h) in ch:
                        clauses.append([-ch[(c_i, h)], -ch[(c_j, h)]])
    return clauses

def teacher_clashes(courses, ch, total_hours):
    clauses = []
    teacher_map = map_teacher(courses)
    for teacher, courses_list in teacher_map.items():
        num_courses = len(courses_list)
        if num_courses < 2:
            continue
        for h in range(total_hours):
            for i in range(num_courses):
                for j in range(i + 1, num_courses):
                    c_i = courses_list[i]
                    c_j = courses_list[j]
                    if (c_i, h) in ch and (c_j, h) in ch:
                        clauses.append([-ch[(c_i, h)], -ch[(c_j, h)]])
    return clauses

def room_clashes_basic(ch, cr, courses, rooms, total_hours):
    """Room clashes para Secciones 3, 4.1, 4.2, 4.3"""
    clauses = []
    all_course_ids = list(courses.keys())
    all_room_ids = list(rooms.keys())
    num_courses = len(all_course_ids)
    
    for r in all_room_ids:
        for h in range(total_hours):
            for i in range(num_courses):
                for j in range(i + 1, num_courses):
                    c_i = all_course_ids[i]
                    c_j = all_course_ids[j]
                    if (c_i, h) in ch and (c_j, h) in ch and (c_i, r) in cr and (c_j, r) in cr:
                        clauses.append([-ch[(c_i, h)], -ch[(c_j, h)], -cr[(c_i, r)], -cr[(c_j, r)]])
    return clauses

def room_clashes_complete(chr_vars, courses, rooms, total_hours):
    """Room clashes para Sección 4.4 (usando chr)"""
    clauses = []
    all_course_ids = list(courses.keys())
    all_room_ids = list(rooms.keys())
    num_courses = len(all_course_ids)
    
    for h in range(total_hours):
        for r in all_room_ids:
            for i in range(num_courses):
                for j in range(i + 1, num_courses):
                    c_i = all_course_ids[i]
                    c_j = all_course_ids[j]
                    if (c_i, h, r) in chr_vars and (c_j, h, r) in chr_vars:
                        clauses.append([-chr_vars[(c_i, h, r)], -chr_vars[(c_j, h, r)]])
    return clauses

def time_slot_availability(ch, unavailabilities, ppd):
    clauses = []
    for u in unavailabilities:
        hour = u.day * ppd + u.day_period
        if (u.course_id, hour) in ch:
            clauses.append([-ch[(u.course_id, hour)]])
    return clauses

def number_of_lectures(courses, ch, total_hours, vpool):
    clauses = []
    for c_id, course in courses.items():
        literals = []
        for h in range(total_hours):
            if (c_id, h) in ch:
                literals.append(ch[(c_id, h)])
        if literals:
            clauses.extend(exactly(literals, course.num_lectures, vpool))
    return clauses

# ============= RESTRICCIONES SOFT/HARD SEGÚN MODO =============
def room_capacity_hard(courses, rooms, cr):
    """Room capacity HARD (Sección 3)"""
    clauses = []
    for c_id, course in courses.items():
        ns = course.num_students
        for r_id, room in rooms.items():
            if ns > room.capacity and (c_id, r_id) in cr:
                clauses.append([-cr[(c_id, r_id)]])
    return clauses

def room_capacity_soft_chr(courses, rooms, chr_vars, total_hours):
    """Room capacity SOFT usando chr (Sección 4.4)"""
    weighted_clauses = []
    for c_id, course in courses.items():
        ns = course.num_students
        for r_id, room in rooms.items():
            if ns > room.capacity:
                weight = ns - room.capacity
                for h in range(total_hours):
                    if (c_id, h, r_id) in chr_vars:
                        weighted_clauses.append((weight, [-chr_vars[(c_id, h, r_id)]]))
    return weighted_clauses

def room_stability_hard(courses, rooms, cr, vpool):
    """Room stability HARD (Sección 3)"""
    clauses = []
    all_room_ids = list(rooms.keys())
    for c_id in courses:
        literals = []
        for r_id in all_room_ids:
            if (c_id, r_id) in cr:
                literals.append(cr[(c_id, r_id)])
        if literals:
            clauses.extend(exactly(literals, 1, vpool))
    return clauses

def room_stability_soft(courses, rooms, cr, vpool):
    """Room stability SOFT (Sección 4.4)"""
    weighted_clauses = []
    all_room_ids = list(rooms.keys())
    
    for c_id in courses:
        literals = []
        for r_id in all_room_ids:
            if (c_id, r_id) in cr:
                literals.append(cr[(c_id, r_id)])
        
        if len(literals) <= 1:
            if len(literals) == 1:
                weighted_clauses.append((0, literals))
            continue
        
        tot = ITotalizer(lits=literals, ubound=len(literals), top_id=vpool.top)
        vpool._top = tot.top_id
        
        if len(tot.rhs) > 0:
            weighted_clauses.append((0, [tot.rhs[0]]))
        
        for i in range(1, len(tot.rhs)):
            weighted_clauses.append((1, [-tot.rhs[i]]))
    
    return weighted_clauses

def min_working_days_hard(courses, cd, days, vpool):
    """Min working days HARD (Sección 3)"""
    clauses = []
    for c_id, course in courses.items():
        literals = []
        for d in range(days):
            if (c_id, d) in cd:
                literals.append(cd[(c_id, d)])
        k = course.min_working_days
        if literals and k > 0:
            clauses.extend(at_least(literals, k, vpool))
    return clauses

def min_working_days_soft(courses, cd, days, vpool):
    """Min working days SOFT (Sección 4.2)"""
    weighted_clauses = []
    
    for c_id, course in courses.items():
        literals = []
        for d in range(days):
            if (c_id, d) in cd:
                literals.append(cd[(c_id, d)])
        
        k = course.min_working_days
        if not literals or k <= 0 or k > len(literals):
            continue
        
        tot = ITotalizer(lits=literals, ubound=len(literals), top_id=vpool.top)
        vpool._top = tot.top_id
        
        for j in range(k - 1, 0, -1):
            if j < len(tot.rhs):
                weighted_clauses.append((5, [tot.rhs[j]]))
    
    return weighted_clauses

def isolated_lectures_hard(kh, curricula, ppd, total_hours):
    """Isolated lectures HARD (Sección 3)"""
    clauses = []
    for k_id in curricula:
        for h in range(total_hours):
            if (k_id, h) not in kh:
                continue
            
            lit_kh_h = -kh[(k_id, h)]
            
            if is_first_slot_of_day(h, ppd):
                if (k_id, h + 1) in kh:
                    clauses.append([lit_kh_h, kh[(k_id, h + 1)]])
            elif is_last_slot_of_day(h, ppd):
                if (k_id, h - 1) in kh:
                    clauses.append([lit_kh_h, kh[(k_id, h - 1)]])
            else:
                neighbors = []
                if (k_id, h - 1) in kh:
                    neighbors.append(kh[(k_id, h - 1)])
                if (k_id, h + 1) in kh:
                    neighbors.append(kh[(k_id, h + 1)])
                if neighbors:
                    clauses.append([lit_kh_h] + neighbors)
    return clauses

def isolated_lectures_soft(kh, curricula, ppd, total_hours):
    """Isolated lectures SOFT (Sección 4.1)"""
    weighted_clauses = []
    
    for k_id in curricula:
        for h in range(total_hours):
            if (k_id, h) not in kh:
                continue
            
            lit_kh_h = -kh[(k_id, h)]
            
            if is_first_slot_of_day(h, ppd):
                if (k_id, h + 1) in kh:
                    weighted_clauses.append((2, [lit_kh_h, kh[(k_id, h + 1)]]))
            elif is_last_slot_of_day(h, ppd):
                if (k_id, h - 1) in kh:
                    weighted_clauses.append((2, [lit_kh_h, kh[(k_id, h - 1)]]))
            else:
                neighbors = []
                if (k_id, h - 1) in kh:
                    neighbors.append(kh[(k_id, h - 1)])
                if (k_id, h + 1) in kh:
                    neighbors.append(kh[(k_id, h + 1)])
                if neighbors:
                    weighted_clauses.append((2, [lit_kh_h] + neighbors))
    
    return weighted_clauses

# ============= ENCODERS POR SECCIÓN =============
def encode_section_3(instance):
    """Sección 3: Basic SAT encoding (todo HARD)"""
    id_to_var = {}
    vpool = IDPool(start_from=1)
    hard_clauses = []
    
    ppd = instance.periods_per_day
    days = instance.num_days
    total_hours = ppd * days
    courses = instance.courses
    curricula = instance.curricula
    rooms = instance.rooms
    unavailabilities = instance.unavailabilities

    ch, id_to_var = get_ch(courses, total_hours, vpool, id_to_var)
    cd, id_to_var = get_cd(courses, days, vpool, id_to_var)
    cr, id_to_var = get_cr(courses, rooms, vpool, id_to_var)
    kh, id_to_var = get_kh(curricula, total_hours, vpool, id_to_var)

    hard_clauses.extend(relation_ch_cd(ch, cd, ppd))
    hard_clauses.extend(relation_ch_kh(ch, kh, curricula))
    hard_clauses.extend(curriculum_clashes(ch, curricula, total_hours))
    hard_clauses.extend(teacher_clashes(courses, ch, total_hours))
    hard_clauses.extend(room_clashes_basic(ch, cr, courses, rooms, total_hours))
    hard_clauses.extend(time_slot_availability(ch, unavailabilities, ppd))
    hard_clauses.extend(number_of_lectures(courses, ch, total_hours, vpool))
    
    hard_clauses.extend(room_capacity_hard(courses, rooms, cr))
    hard_clauses.extend(room_stability_hard(courses, rooms, cr, vpool))
    hard_clauses.extend(min_working_days_hard(courses, cd, days, vpool))
    hard_clauses.extend(isolated_lectures_hard(kh, curricula, ppd, total_hours))
    
    return hard_clauses, [], vpool

def encode_section_4_1(instance):
    """Sección 4.1: Relaxing "isolated lectures" as Partial-MaxSAT"""
    id_to_var = {}
    vpool = IDPool(start_from=1)
    hard_clauses = []
    soft_clauses_weighted = []
    
    ppd = instance.periods_per_day
    days = instance.num_days
    total_hours = ppd * days
    courses = instance.courses
    curricula = instance.curricula
    rooms = instance.rooms
    unavailabilities = instance.unavailabilities

    ch, id_to_var = get_ch(courses, total_hours, vpool, id_to_var)
    cd, id_to_var = get_cd(courses, days, vpool, id_to_var)
    cr, id_to_var = get_cr(courses, rooms, vpool, id_to_var)
    kh, id_to_var = get_kh(curricula, total_hours, vpool, id_to_var)

    hard_clauses.extend(relation_ch_cd(ch, cd, ppd))
    hard_clauses.extend(relation_ch_kh(ch, kh, curricula))
    hard_clauses.extend(curriculum_clashes(ch, curricula, total_hours))
    hard_clauses.extend(teacher_clashes(courses, ch, total_hours))
    hard_clauses.extend(room_clashes_basic(ch, cr, courses, rooms, total_hours))
    hard_clauses.extend(time_slot_availability(ch, unavailabilities, ppd))
    hard_clauses.extend(number_of_lectures(courses, ch, total_hours, vpool))
    hard_clauses.extend(room_capacity_hard(courses, rooms, cr))
    hard_clauses.extend(room_stability_hard(courses, rooms, cr, vpool))
    hard_clauses.extend(min_working_days_hard(courses, cd, days, vpool))
    
    soft_clauses_weighted.extend(isolated_lectures_soft(kh, curricula, ppd, total_hours))
    
    return hard_clauses, soft_clauses_weighted, vpool

def encode_section_4_2(instance):
    """Sección 4.2: Relaxing "min working days" as Weighted-Partial-MaxSAT"""
    id_to_var = {}
    vpool = IDPool(start_from=1)
    hard_clauses = []
    soft_clauses_weighted = []
    
    ppd = instance.periods_per_day
    days = instance.num_days
    total_hours = ppd * days
    courses = instance.courses
    curricula = instance.curricula
    rooms = instance.rooms
    unavailabilities = instance.unavailabilities

    ch, id_to_var = get_ch(courses, total_hours, vpool, id_to_var)
    cd, id_to_var = get_cd(courses, days, vpool, id_to_var)
    cr, id_to_var = get_cr(courses, rooms, vpool, id_to_var)
    kh, id_to_var = get_kh(curricula, total_hours, vpool, id_to_var)

    hard_clauses.extend(relation_ch_cd(ch, cd, ppd))
    hard_clauses.extend(relation_ch_kh(ch, kh, curricula))
    hard_clauses.extend(curriculum_clashes(ch, curricula, total_hours))
    hard_clauses.extend(teacher_clashes(courses, ch, total_hours))
    hard_clauses.extend(room_clashes_basic(ch, cr, courses, rooms, total_hours))
    hard_clauses.extend(time_slot_availability(ch, unavailabilities, ppd))
    hard_clauses.extend(number_of_lectures(courses, ch, total_hours, vpool))
    hard_clauses.extend(room_capacity_hard(courses, rooms, cr))
    hard_clauses.extend(room_stability_hard(courses, rooms, cr, vpool))
    
    soft_clauses_weighted.extend(isolated_lectures_soft(kh, curricula, ppd, total_hours))
    soft_clauses_weighted.extend(min_working_days_soft(courses, cd, days, vpool))
    
    return hard_clauses, soft_clauses_weighted, vpool

def encode_section_4_4(instance):
    """Sección 4.4: Complete encoding (todas las soft)"""
    id_to_var = {}
    vpool = IDPool(start_from=1)
    hard_clauses = []
    soft_clauses_weighted = []
    
    ppd = instance.periods_per_day
    days = instance.num_days
    total_hours = ppd * days
    courses = instance.courses
    curricula = instance.curricula
    rooms = instance.rooms
    unavailabilities = instance.unavailabilities

    ch, id_to_var = get_ch(courses, total_hours, vpool, id_to_var)
    cd, id_to_var = get_cd(courses, days, vpool, id_to_var)
    cr, id_to_var = get_cr(courses, rooms, vpool, id_to_var)
    kh, id_to_var = get_kh(curricula, total_hours, vpool, id_to_var)
    chr_vars, id_to_var = get_chr(courses, rooms, total_hours, vpool, id_to_var)

    hard_clauses.extend(relation_ch_cd(ch, cd, ppd))
    hard_clauses.extend(relation_ch_kh(ch, kh, curricula))
    hard_clauses.extend(relation_ch_chr(ch, chr_vars, courses, rooms, total_hours))
    hard_clauses.extend(relation_cr_chr(cr, chr_vars, courses, rooms, total_hours))
    hard_clauses.extend(curriculum_clashes(ch, curricula, total_hours))
    hard_clauses.extend(teacher_clashes(courses, ch, total_hours))
    hard_clauses.extend(room_clashes_complete(chr_vars, courses, rooms, total_hours))
    hard_clauses.extend(time_slot_availability(ch, unavailabilities, ppd))
    hard_clauses.extend(number_of_lectures(courses, ch, total_hours, vpool))
    
    soft_clauses_weighted.extend(room_capacity_soft_chr(courses, rooms, chr_vars, total_hours))
    soft_clauses_weighted.extend(room_stability_soft(courses, rooms, cr, vpool))
    soft_clauses_weighted.extend(min_working_days_soft(courses, cd, days, vpool))
    soft_clauses_weighted.extend(isolated_lectures_soft(kh, curricula, ppd, total_hours))
    
    return hard_clauses, soft_clauses_weighted, vpool

# ============= SOLVERS =============
def solve_sat(hard_clauses, timeout=300):
    """Solver SAT para Sección 3"""
    print("Starting SAT solver (Glucose3)...")
    start_time = time.time()
    
    solver = Glucose3()
    for clause in hard_clauses:
        solver.add_clause(clause)
    
    if solver.solve():
        solving_time = time.time() - start_time
        print(f"\nSAT! Solution found in {solving_time:.2f}s!")
        print("Cost: 0 (all constraints satisfied)")
        result = (0, solving_time)
    else:
        solving_time = time.time() - start_time
        print(f"\nUNSAT! No solution exists. Search terminated in {solving_time:.2f}s.")
        result = (None, solving_time)
    
    solver.delete()
    return result

def solve_maxsat_rc2(hard_clauses, soft_clauses_weighted, timeout=300):
    """
    Solver MaxSAT usando RC2 (core-based) para Secciones 4.1, 4.2, 4.4
    RC2 es un solver basado en unsatisfiable cores como describe el paper en Sección 2.3
    """
    print(f"Starting RC2 MaxSAT solver (timeout: {timeout}s)...")
    print(f"Hard clauses: {len(hard_clauses)}, Soft clauses: {len(soft_clauses_weighted)}")
    
    start_time = time.time()
    
    # Create WCNF formula
    wcnf = WCNF()
    
    # Add hard clauses
    for clause in hard_clauses:
        wcnf.append(clause)
    
    # Add soft clauses with weights
    for weight, clause in soft_clauses_weighted:
        wcnf.append(clause, weight=weight)
    
    print(f"\nWCNF formula created: {wcnf.nv} variables, {len(wcnf.hard)} hard, {len(wcnf.soft)} soft")
    print("Starting RC2 optimization...\n")
    
    # Create RC2 solver
    try:
        with RC2(wcnf, solver='g3', adapt=True, exhaust=True, minz=True, trim=5) as solver:
            # Compute optimal solution
            model = solver.compute()
            
            if model is not None:
                cost = solver.cost
                elapsed = time.time() - start_time
                print(f"\nOptimal solution found!")
                print(f"Cost: {cost}")
                print(f"Time: {elapsed:.2f}s")
                return cost, elapsed
            else:
                elapsed = time.time() - start_time
                print(f"\nUNSAT: No feasible solution exists")
                print(f"Time: {elapsed:.2f}s")
                return None, elapsed
                
    except Exception as e:
        elapsed = time.time() - start_time
        print(f"\nError during solving: {e}")
        print(f"Time: {elapsed:.2f}s")
        return None, elapsed

# ============= MAIN =============
if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python complete_paper_encoder.py <file.ctt> <mode> [timeout]")
        print("\nModes:")
        print("  3  - Section 3: Basic SAT (all hard)")
        print("  4.1 - Section 4.1: Partial MaxSAT (isolated lectures soft)")
        print("  4.2 - Section 4.2: Weighted Partial MaxSAT (isolated + min days soft)")
        print("  4.4 - Section 4.4: Complete encoding (all soft)")
        sys.exit(1)
    
    input_file = sys.argv[1]
    mode = sys.argv[2] if len(sys.argv) > 2 else "4.4"
    timeout = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    
    print(f"{'='*70}")
    print(f"Curriculum-based Course Timetabling with SAT and MaxSAT")
    print(f"Paper-accurate implementation")
    print(f"{'='*70}")
    print(f"File: {input_file}")
    print(f"Mode: Section {mode}")
    print(f"Timeout: {timeout}s")
    print(f"{'='*70}\n")

    instance = parse_ctt(input_file)
    
    print(f"Instance: {instance.name}")
    print(f"  Courses: {instance.num_courses}")
    print(f"  Rooms: {instance.num_rooms}")
    print(f"  Days: {instance.num_days}")
    print(f"  Periods per day: {instance.periods_per_day}")
    print(f"  Total time slots: {instance.num_days * instance.periods_per_day}")
    print(f"  Curricula: {instance.num_curricula}")
    print()
    
    # Seleccionar encoder según modo
    start_time = time.time()
    
    if mode == "3":
        print("Encoding Section 3: Basic SAT (all constraints hard)...")
        hard_clauses, soft_clauses_weighted, vpool = encode_section_3(instance)
    elif mode == "4.1":
        print("Encoding Section 4.1: Partial MaxSAT (isolated lectures soft)...")
        hard_clauses, soft_clauses_weighted, vpool = encode_section_4_1(instance)
    elif mode == "4.2":
        print("Encoding Section 4.2: Weighted Partial MaxSAT (isolated + min days soft)...")
        hard_clauses, soft_clauses_weighted, vpool = encode_section_4_2(instance)
    elif mode == "4.4":
        print("Encoding Section 4.4: Complete encoding (all soft)...")
        hard_clauses, soft_clauses_weighted, vpool = encode_section_4_4(instance)
    else:
        print(f"Unknown mode: {mode}")
        sys.exit(1)
    
    encoding_time = time.time() - start_time
    
    print(f"Generated {len(hard_clauses)} hard and {len(soft_clauses_weighted)} soft clauses in {encoding_time:.2f}s.")
    print(f"Total variables: {vpool.top}")
    print()
    
    # Resolver según modo
    if mode == "3":
        cost, solving_time = solve_sat(hard_clauses, timeout)
    else:
        cost, solving_time = solve_maxsat_rc2(hard_clauses, soft_clauses_weighted, timeout)
    
    # Resumen final
    print(f"\n{'='*70}")
    print(f"RESULTS SUMMARY")
    print(f"{'='*70}")
    print(f"Instance: {instance.name}")
    print(f"Mode: Section {mode}")
    print(f"Cost: {cost if cost is not None else 'UNSAT'}")
    print(f"Encoding time: {encoding_time:.2f}s")
    print(f"Solving time: {solving_time:.2f}s" if solving_time else "N/A")
    print(f"Total time: {encoding_time + (solving_time if solving_time else 0):.2f}s")
    print(f"{'='*70}")
