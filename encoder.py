from classes_ctt import Instance, parse_ctt
from utils import hour_for_day, day, teacher, map_teacher
import time

def encoder(instance: Instance):
    id_to_var = {}
    n_var = 1
    clauses = []
    ppd = instance.periods_per_day
    total_hours =  ppd * instance.num_days
    courses = instance.courses
    curricula = instance.curricula
    # Creacion de las variables
    ch, n_var, id_to_var = get_ch(courses, total_hours, n_var, id_to_var)
    cd, n_var, id_to_var = get_cd(courses, instance.num_days, n_var, id_to_var)
    cr, n_var, id_to_var = get_cr(courses, instance.rooms, n_var, id_to_var)
    kh, n_var, id_to_var = get_kh(instance.curricula, total_hours, n_var, id_to_var)
    # Creacion de clausulas a partir de relaciones
    clauses.extend(relation_ch_cd(ch, cd, ppd)) 
    clauses.extend(relation_ch_kh(ch, kh, curricula)) 
    clauses.extend(curriculum_clashes(ch, curricula))
    clauses.extend(teacher_clashes(courses, ch))
    print(clauses, len(clauses))

def teacher_clashes(courses, ch):
    clauses = []
    c = list(courses.keys())
    num_courses = len(c)
    teacher_map = map_teacher(courses=courses)
    hours = [h for (c, h) in ch.keys()]
    for teacher_id, courses_list in teacher_map.items():
        num_courses = len(courses_list)
        if num_courses < 2:
            continue
        for h in hours:
            for i in range(num_courses):
                for j in range(i+1, num_courses):
                    c_i = c[i]
                    c_j = c[j]
                    if (c_i, h) in ch and (c_j, h) in ch:
                        id_ci_h = ch[(c_i, h)]
                        id_cj_h = ch[(c_j, h)]
                        clauses.append([-id_ci_h, -id_cj_h])
    return clauses



def curriculum_clashes(ch, curricula):
    clauses = []
    for curriculum in curricula:
        courses = list(curricula[curriculum].courses)
        num_courses = len(courses)
        hours = [h for (c, h) in ch]
        for h in hours:
            for i in range(num_courses):
                for j in range(i + 1, num_courses):
                    c_i = courses[i]
                    c_j = courses[j]
                    if (c_i, h) in ch and (c_j, h) in ch:
                        clause = [-ch[(c_i, h)], -ch[(c_j, h)]]
                        clauses.append(clause)
    return clauses

def relation_ch_kh(ch, kh, curricula):
    clauses = []
    for (c, h) in ch:
        ks = c_in_k(c, curricula)
        lit_ch = -ch[(c, h)]
        for k in ks:
            if (k, h) in kh:
                clauses.append([lit_ch, kh[(k, h)]])
    ## Al menos uno debe ser verdadero
    for (k, h) in kh:
        courses = curricula[k].courses
        if len(courses) > 0:
            lit_kh = -kh[(k, h)]
            aux = [ch[course, h] for course in courses]
            clause = [lit_kh]
            clause.extend(aux)
            clauses.append(clause)
    return clauses

def c_in_k(c, curricula):
    out = []
    for k in curricula:
        curriculum = curricula[k]
        for course in curriculum.courses:
            if c == course:
                out.append(k)
    return out


def relation_ch_cd(ch, cd, ppd):
    """
    Obtiene las clausulas a partir de las relaciones ch y cd
    input:
        ch: diccionario cuyas llaves son una tupla (clase, hora), el valor es la variable que representa
        cd: diccionario cuyas llaves son una tupla (clase, dia), el valor es la variable que representa
        ppd: entero que indica la cantidad de periodos por dia
    output:
        clauses: lista de clausulas para agregar
    """
    clauses = []
    # Ciclo para la primera relacion: si una clase se hace en una hora de un dia d, entonces esa clase se da en el dia d
    for prop in ch:
        c, h = prop
        d = day(h, ppd)
        clause = [-ch[prop], cd[(c, d)]]
        clauses.append(clause)
    # Ciclo segunda relacion: Si una clase se da en un dia d, entonces se da en alguna hora del dia d
    for prop in cd:
        c, d = prop
        hours = hour_for_day(d, ppd)
        aux = [ch[(c, h)] for h in hours]
        clause = [-cd[prop]]
        clause.extend(aux)
        clauses.append(clause)
    return clauses  

def get_ch(courses, hours, n_var, id_to_var):
    ch = {}
    for c in courses:
        for h in range(hours):
            ch[(c, h)] = n_var
            id_to_var[n_var] = ('ch', c, h)
            n_var += 1
    return ch, n_var, id_to_var

def get_cd(courses, days, n_var, id_to_var):
    cd = {}
    for c in courses:
        for d in range(days):
            cd[(c, d)] = n_var
            id_to_var[n_var] = ('cd', c, d)
            n_var += 1
    return cd, n_var, id_to_var

def get_cr(courses, rooms, n_var, id_to_var):
    cr = {}
    for c in courses:
        for r in rooms:
            cr[(c, r)] = n_var
            id_to_var[n_var] = ('cr', c, r)
            n_var += 1
    return cr, n_var, id_to_var

def get_kh(curricula, hours, n_var, id_to_var):
    kh = {}
    for k in curricula:
        for h in range(hours):
            kh[(k, h)] = n_var
            id_to_var[n_var] = ('kh', k, h)
            n_var += 1
    return kh, n_var, id_to_var

if __name__ == "__main__":
    print("HOLA")
    prueba = parse_ctt("toy.txt")
    encoder(prueba)