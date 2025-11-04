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

def at_least(k, lits, vpool):
    cnf = CardEnc.atleast(lits=lits, bound=k, encoding=3, vpool=vpool)
    return cnf.clauses

def is_first_slot_of_day(h, ppd):
    return h % ppd == 0

def is_last_slot_of_day(h, ppd):
    return (h + 1) % ppd == 0

# Contenido de utils.py (tu función parse_xml debe estar aquí arriba)

# ... (la función parse_xml que ya existe)

# >>> AÑADE LA NUEVA FUNCIÓN AQUÍ ABAJO <<<

def decode_solution(model, var_map, data):
    """
    Traduce el modelo de PySAT a un horario legible.

    Args:
        model (list): La lista de literales del modelo encontrado por el solver.
        var_map (dict): El mapeo de (tipo, c, h/r) -> ID numérico.
        data (dict): El diccionario con los datos parseados del XML.
    """
    reverse_var_map = {v: k for k, v in var_map.items()}
    course_to_room = {}
    schedule = {}

    true_vars = [var for var in model if var > 0]

    # Paso A: Encontrar la asignación de sala para cada curso
    for var_id in true_vars:
        if var_id in reverse_var_map:
            var_name = reverse_var_map[var_id]
            var_type = var_name[0]
            if var_type == 'cr':
                _, course, room = var_name
                course_to_room[course] = room

    # Paso B: Construir el horario
    for var_id in true_vars:
        if var_id in reverse_var_map:
            var_name = reverse_var_map[var_id]
            var_type = var_name[0]
            if var_type == 'ch':
                _, course, timeslot = var_name
                if timeslot not in schedule:
                    schedule[timeslot] = []
                room = course_to_room.get(course, 'SALA_DESCONOCIDA')
                schedule[timeslot].append({'course': course, 'room': room})

    print("\n" + "="*25)
    print("  HORARIO GENERADO")
    print("="*25 + "\n")

    days_order = [d['id'] for d in data['days']]
    timeslots_by_day = {day_id: [] for day_id in days_order}
    for ts in data['time_slots']:
        timeslots_by_day[ts['day']].append(ts)

    for day_id in days_order:
        day_name = next(d['name'] for d in data['days'] if d['id'] == day_id)
        print(f"--- {day_name.upper()} ---")
        
        day_timeslots = sorted(timeslots_by_day[day_id], key=lambda x: x['start'])

        for ts in day_timeslots:
            ts_id = ts['id']
            ts_name = ts['name']
            if ts_id in schedule:
                for entry in schedule[ts_id]:
                    course_id = entry['course']
                    room_id = entry['room']
                    print(f"  {ts_name}: Curso '{course_id}' en Aula '{room_id}'")
        print()