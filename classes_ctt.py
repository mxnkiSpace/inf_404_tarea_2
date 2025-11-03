from dataclasses import dataclass
from typing import Dict, List, Set
'''
Courses: <CourseID> <Teacher> <# Lectures> <MinWorkingDays> <# Students>
Rooms: <RoomID> <Capacity>
Curricula: <CurriculumID> <# Courses> <MemberID> ... <MemberID>
Unavailability_Constraints: <CourseID> <Day> <Day_Period>
'''

@dataclass
class Course:
    #name: str
    teacher: str
    num_lectures: int  
    min_working_days: int 
    num_students: int  

@dataclass
class Room:
    #name: str
    capacity: int

@dataclass
class Curriculum:
    #name: str
    #num_courses: int
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
                    state = l[0]
                    state = state[:-1]
                    continue
                else:
                    break
            
            if state == 'INFO':
                key = l[0].lower()
                key = key[:-1]
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
        name = info['name'],
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



if __name__ == "__main__":
    print(parse_ctt("toy.txt"))