from math import ceil
from pysat.card import CardEnc

def day(h, ppd):
    """
    Retorna el dia al que corresponde la hora h. Se usa en encoder.py
    Input:
        h: entero que indica la hora correspondiente
        ppd: entero periods_per_day que indica los periodos que tiene un dia
    Output:
        ceil((h+1)/ppd) - 1: toma valores del 0 al total de horas -1
    """
    return ceil((h+1)/ppd) - 1 

def hour_for_day(d, ppd):
    """
    Retorna una lista con las horas que pertenece al dia d. Se usa en encoder.py
    Input:
        d: entero que indica el dia correspondiente
        ppd: entero periods_per_day que indica los periodos que tiene un dia
    Output:
        list(range(start, end)): la lista de horas
    """
    start = d*ppd
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

def exactly(k, literals, vpool):

    cnf = CardEnc.equals(lits=literals, encoding=3, bound=k, vpool=vpool)

    return cnf.clauses