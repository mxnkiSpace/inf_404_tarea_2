from classes_ctt import Instance, parse_ctt
import time
from math import ceil

def encoder(instance: Instance):
    id_to_var = {}
    n_var = 1
    total_hours = instance.periods_per_day * instance.num_days
    courses = instance.courses
    ch, n_var, id_to_var = get_ch(courses, total_hours, n_var, id_to_var)
    cd, n_var, id_to_var = get_cd(courses, instance.num_days, n_var, id_to_var)
    cr, n_var, id_to_var = get_cr(courses, instance.rooms, n_var, id_to_var)
    kh, n_var, id_to_var = get_kh(instance.curricula, total_hours, n_var, id_to_var)
    print(id_to_var)

#print(f"La clase {i} se dicta en el horario {j+1} del día {k+1}")

def day(h, periods_per_day):
    return ceil(h/periods_per_day)

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