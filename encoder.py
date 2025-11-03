from classes_ctt import Instance, parse_ctt
import time
from math import ceil

def encoder(instance: Instance):
    id_to_var = {}
    n_var = 1
    clauses = []
    ppd = instance.periods_per_day
    total_hours =  ppd * instance.num_days
    courses = instance.courses
    # Creacion de las variables
    ch, n_var, id_to_var = get_ch(courses, total_hours, n_var, id_to_var)
    cd, n_var, id_to_var = get_cd(courses, instance.num_days, n_var, id_to_var)
    cr, n_var, id_to_var = get_cr(courses, instance.rooms, n_var, id_to_var)
    kh, n_var, id_to_var = get_kh(instance.curricula, total_hours, n_var, id_to_var)
    #print(cd)
    clauses.extend(relation_ch_cd(ch, cd, ppd))  
    print(clauses, len(clauses))

#print(f"La clase {i} se dicta en el horario {j+1} del día {k+1}")

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

# Retorna el dia al que pertenece la hora
def day(h, periods_per_day):
    return ceil((h+1)/periods_per_day) - 1 

def hour_for_day(d, ppd):
    start = d*ppd
    end = start + ppd
    return list(range(start, end))

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