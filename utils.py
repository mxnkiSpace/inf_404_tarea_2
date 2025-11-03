from math import ceil

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