# complete_encoder_corrected.py - Versión corregida

import sys
import time
from dataclasses import dataclass
from typing import Dict, List
from math import ceil
from pysat.formula import IDPool, WCNF
from pysat.card import CardEnc, EncType, ITotalizer
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

# ============= ENCODER =============
def encoder(instance: Instance, type_sat: int = 0):
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
    hard_clauses.extend(room_clashes(ch, cr, courses, rooms, total_hours))

    hard_clauses.extend(time_slot_availability(ch, unavailabilities, ppd))
    hard_clauses.extend(number_of_lectures(courses, ch, total_hours, vpool))

    if type_sat == 0:  # SAT puro: todo es hard
        hard_clauses.extend(room_capacity_hard(courses, rooms, cr))
        hard_clauses.extend(room_stability_hard(courses, rooms, cr, vpool))
        hard_clauses.extend(min_working_days_hard(courses, cd, days, vpool))
        hard_clauses.extend(isolated_lectures_hard(kh, curricula, ppd, total_hours))
        return hard_clauses, [], vpool

    elif type_sat == 1:  # MaxSAT: restricciones soft
        soft_clauses_weighted.extend(room_capacity_soft(courses, rooms, cr))
        
        soft_clauses_weighted.extend(room_stability_soft(courses, rooms, cr, vpool))
        
        soft_clauses_weighted.extend(min_working_days_soft(courses, cd, days, vpool))
        
        soft_clauses_weighted.extend(isolated_lectures_soft(kh, curricula, ppd, total_hours))
        
        return hard_clauses, soft_clauses_weighted, vpool

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
    # Si curso c está en hora h, entonces curriculum k está en hora h
    for (c, h) in ch:
        for k, curr in curricula.items():
            if c in curr.courses:
                if (k, h) in kh:
                    clauses.append([-ch[(c, h)], kh[(k, h)]])
    
    # Si curriculum k está en hora h, al menos un curso de k está en h
    for (k, h) in kh:
        courses_k = curricula[k].courses
        clause = [-kh[(k, h)]]
        for c in courses_k:
            if (c, h) in ch:
                clause.append(ch[(c, h)])
        clauses.append(clause)
    return clauses

# ============= RESTRICCIONES DURAS =============
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

def room_clashes(ch, cr, courses_dict, rooms_dict, total_hours):
    clauses = []
    all_course_ids = list(courses_dict.keys())
    all_room_ids = list(rooms_dict.keys())
    num_courses = len(all_course_ids)
    
    for h in range(total_hours):
        for r in all_room_ids:
            for i in range(num_courses):
                for j in range(i + 1, num_courses):
                    c_i = all_course_ids[i]
                    c_j = all_course_ids[j]
                    if (c_i, h) in ch and (c_j, h) in ch and (c_i, r) in cr and (c_j, r) in cr:
                        clause = [-ch[(c_i, h)], -ch[(c_j, h)], -cr[(c_i, r)], -cr[(c_j, r)]]
                        clauses.append(clause)
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

# ============= RESTRICCIONES HARD (para SAT puro) =============
def room_capacity_hard(courses, rooms, cr):
    clauses = []
    for c_id, course in courses.items():
        ns = course.num_students
        for r_id, room in rooms.items():
            if (c_id, r_id) in cr and ns > room.capacity:
                clauses.append([-cr[(c_id, r_id)]])
    return clauses

def room_stability_hard(courses, rooms, cr, vpool):
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

def min_working_days_hard(courses, cd, days, vpool):
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

def isolated_lectures_hard(kh, curricula, ppd, total_hours):
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

# ============= RESTRICCIONES SOFT (para MaxSAT) =============
def room_capacity_soft(courses, rooms, cr):
    """Penaliza 1 por cada estudiante que no cabe en la sala"""
    weighted_clauses = []
    for c_id, course in courses.items():
        ns = course.num_students
        for r_id, room in rooms.items():
            if (c_id, r_id) in cr and ns > room.capacity:
                weight = ns - room.capacity
                weighted_clauses.append((weight, [-cr[(c_id, r_id)]]))
    return weighted_clauses

def room_stability_soft(courses, rooms, cr, vpool):
    """Penaliza 1 por cada sala extra usada (más allá de la primera)"""
    weighted_clauses = []
    all_room_ids = list(rooms.keys())
    
    for c_id in courses:
        literals = []
        for r_id in all_room_ids:
            if (c_id, r_id) in cr:
                literals.append(cr[(c_id, r_id)])
        
        if len(literals) <= 1:
            continue
        
        # Al menos una sala debe ser asignada (hard)
        weighted_clauses.append((0, literals))  # Peso 0 = hard en WCNF
        
        # Penalizar usar más de una sala
        for i in range(len(literals)):
            for j in range(i + 1, len(literals)):
                # Si ambas salas son usadas, costo de 1
                weighted_clauses.append((1, [-literals[i], -literals[j]]))
    
    return weighted_clauses

def min_working_days_soft(courses, cd, days, vpool):
    """Penaliza 5 por cada día menos del mínimo requerido"""
    weighted_clauses = []
    
    for c_id, course in courses.items():
        literals = []
        for d in range(days):
            if (c_id, d) in cd:
                literals.append(cd[(c_id, d)])
        
        k = course.min_working_days
        if not literals or k <= 0 or k > len(literals):
            continue
        
        # Crear totalizer para contar días usados
        from pysat.card import ITotalizer
        
        tot = ITotalizer(lits=literals, ubound=len(literals), top_id=vpool.top)
        vpool._top = tot.top_id
        
        # Penalizar por cada día menos de k
        # tot.rhs[i] es true si se usan al menos i+1 días
        # Queremos penalizar cuando se usan menos de k días
        for j in range(k):
            # Si tot.rhs[j] es false, significa que se usan <= j días
            # Penalizar con peso 5 por cada día faltante
            if j < len(tot.rhs):
                weighted_clauses.append((5, [tot.rhs[j]]))
    
    return weighted_clauses

def isolated_lectures_soft(kh, curricula, ppd, total_hours):
    """Penaliza 2 por cada lectura aislada"""
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

def iterative_maxsat_solver(wcnf, timeout=300):
    """
    Solver iterativo simplificado que encuentra soluciones progresivamente mejores.
    """
    from pysat.solvers import Glucose3
    
    print(f"Using iterative solver with {timeout}s timeout...")
    
    start_time = time.time()
    best_cost = float('inf')
    best_model = None
    
    hard_clauses = []
    soft_clauses = []
    soft_weights = []
    
    # wcnf.hard contiene las cláusulas hard
    # wcnf.soft contiene las cláusulas soft
    # wcnf.wght contiene los pesos (top_weight para hard, peso real para soft)
    
    top_weight = max(wcnf.wght) if wcnf.wght else 1
    
    for i, clause in enumerate(wcnf.soft):
        weight = wcnf.wght[i]
        if weight >= top_weight:
            hard_clauses.append(clause)
        else:
            soft_clauses.append(clause)
            soft_weights.append(weight)
    
    print(f"Hard clauses: {len(hard_clauses)}, Soft clauses: {len(soft_clauses)}")
    print(f"Total soft weight: {sum(soft_weights)}")
    
    # Paso 1: Encontrar cualquier solución satisfacible
    print("\nStep 1: Finding initial feasible solution...")
    solver = Glucose3()
    
    for clause in hard_clauses:
        solver.add_clause(clause)
    
    if not solver.solve():
        print("UNSAT: No feasible solution exists (hard clauses are contradictory)")
        solver.delete()
        return None, None
    
    model = solver.get_model()
    model_set = set(model)
    cost = 0
    
    for i, clause in enumerate(soft_clauses):
        # Una cláusula está satisfecha si al menos un literal está en el modelo
        satisfied = any(lit in model_set for lit in clause)
        if not satisfied:
            cost += soft_weights[i]
    
    best_cost = cost
    best_model = model
    elapsed = time.time() - start_time
    print(f"Initial solution found! Cost: {best_cost} (time: {elapsed:.2f}s)")
    
    # Paso 2: Mejorar iterativamente
    print("\nStep 2: Improving solution iteratively...")
    iteration = 0
    max_iterations = 100  # Límite de iteraciones
    
    while iteration < max_iterations:
        elapsed = time.time() - start_time
        if elapsed > timeout:
            print(f"\nTimeout reached ({timeout}s). Returning best solution found.")
            break
        
        iteration += 1
        
        if best_cost == 0:
            print("\nOptimal solution found (cost = 0)!")
            break
        
        print(f"  Iteration {iteration}: Searching for solution with cost < {best_cost}...", end=" ", flush=True)
        
        # Crear nuevo solver con constraint de costo
        solver.delete()
        solver = Glucose3()
        
        for clause in hard_clauses:
            solver.add_clause(clause)
        
        # Agregar soft clauses con variables de relajación
        max_var = max(max(abs(lit) for lit in clause) for clause in hard_clauses + soft_clauses)
        relaxation_vars = []
        
        for i, clause in enumerate(soft_clauses):
            relax_var = max_var + i + 1
            relaxation_vars.append((relax_var, soft_weights[i]))
            # clause OR relax_var
            solver.add_clause(clause + [relax_var])
        
        # Agregar constraint: suma ponderada de vars de relajación < best_cost
        # Esto es difícil sin PB constraints, así que usamos enfoque simple:
        # Intentar encontrar cualquier solución y verificar su costo
        
        found_better = False
        attempts = 0
        max_attempts = 10
        
        while attempts < max_attempts and solver.solve():
            attempts += 1
            model = solver.get_model()
            model_set = set(model)
            
            # Calcular costo de esta solución
            cost = 0
            for i, clause in enumerate(soft_clauses):
                satisfied = any(lit in model_set for lit in clause)
                if not satisfied:
                    cost += soft_weights[i]
            
            if cost < best_cost:
                best_cost = cost
                best_model = model
                elapsed = time.time() - start_time
                print(f"Better! Cost: {best_cost} (time: {elapsed:.2f}s)")
                found_better = True
                break
            else:
                # Bloquear esta solución y buscar otra
                blocking_clause = []
                for i, (relax_var, _) in enumerate(relaxation_vars):
                    if relax_var in model_set:
                        blocking_clause.append(-relax_var)
                    else:
                        blocking_clause.append(relax_var)
                
                if blocking_clause:
                    solver.add_clause(blocking_clause)
        
        if not found_better:
            print("No improvement found.")
            break
    
    solver.delete()
    elapsed = time.time() - start_time
    print(f"\nSearch completed in {elapsed:.2f}s")
    return best_model, best_cost

# ============= MAIN =============
if __name__ == "__main__":
    input_file = sys.argv[1] if len(sys.argv) > 1 else "toy.txt"
    mode = int(sys.argv[2]) if len(sys.argv) > 2 else 1  # 0=SAT, 1=MaxSAT
    timeout = int(sys.argv[3]) if len(sys.argv) > 3 else 300  # timeout en segundos
    
    print(f"--- Running Encoder ({'SAT' if mode == 0 else 'MaxSAT'} mode) on: {input_file} ---")

    instance = parse_ctt(input_file)
    
    print(f"Encoding '{instance.name}'...")
    print(f"  Courses: {instance.num_courses}")
    print(f"  Rooms: {instance.num_rooms}")
    print(f"  Days: {instance.num_days}")
    print(f"  Periods per day: {instance.periods_per_day}")
    print(f"  Total time slots: {instance.num_days * instance.periods_per_day}")
    
    start_time = time.time()
    hard_clauses, soft_clauses_weighted, vpool = encoder(instance, type_sat=mode)
    encoding_time = time.time() - start_time
    
    print(f"\nGenerated {len(hard_clauses)} hard and {len(soft_clauses_weighted)} soft clauses in {encoding_time:.2f}s.")
    print(f"Total variables: {vpool.top}")

    if mode == 0:  # SAT puro
        print("\nPreparing CNF formula...")
        from pysat.solvers import Glucose3
        
        print("Starting SAT solver...")
        start_time = time.time()
        solver = Glucose3()
        for clause in hard_clauses:
            solver.add_clause(clause)
        
        if solver.solve():
            solving_time = time.time() - start_time
            print(f"\nSAT! Solution found in {solving_time:.2f}s!")
            print("Cost: 0 (all constraints satisfied)")
        else:
            solving_time = time.time() - start_time
            print(f"\nUNSAT! No solution exists. Search terminated in {solving_time:.2f}s.")
        solver.delete()
    
    else:  # MaxSAT
        print("\nPreparing WCNF formula...")
        wcnf = WCNF()
        
        # Top weight (mayor que la suma de todos los pesos soft)
        top_weight = sum(w for w, _ in soft_clauses_weighted) + 1
        
        for clause in hard_clauses:
            wcnf.append(clause, weight=top_weight)
        
        for weight, clause in soft_clauses_weighted:
            wcnf.append(clause, weight=weight)
        
        print(f"WCNF: {len(hard_clauses)} hard clauses (weight={top_weight}), {len(soft_clauses_weighted)} soft clauses")
        
        print(f"\nStarting iterative MaxSAT solver (timeout: {timeout}s)...")
        start_time = time.time()
        
        try:
            model, cost = iterative_maxsat_solver(wcnf, timeout=timeout)
            
            if model:
                solving_time = time.time() - start_time
                print(f"\n{'='*60}")
                print(f"SOLUTION FOUND!")
                print(f"Cost: {cost}")
                print(f"Total time: {solving_time:.2f}s")
                print(f"{'='*60}")
            else:
                solving_time = time.time() - start_time
                print(f"\nUNSAT! Problem has no solution. Search terminated in {solving_time:.2f}s.")
                print("This indicates a contradiction in the HARD clauses.")
        except Exception as e:
            print(f"\nError during solving: {e}")
            import traceback
            traceback.print_exc()
