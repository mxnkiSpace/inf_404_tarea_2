from dataclasses import dataclass

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
    num_courses: int
    courses: set

@dataclass
class Unavailability:
    course_name: str
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

    courses: dict
    rooms: dict
    curricula: dict 
    unavailabilyties: set


def parse_ctt(file_name):
    info = []
    courses = {}
    rooms = {}
    curricula = {}
    unavailabilyties = []

    flag_info = True
    flag_courses = False
    flag_rooms = False
    flag_curricula = False
    flag_unavai = False
    with open(file_name) as file:
        for line in file:
            l = line.strip().split()
            if not l:
                continue

            if l[0] == "COURSES:":
                flag_info = False
                flag_courses = True
                continue
            if l[0] == "ROOMS:":
                flag_courses = False
                flag_rooms = True
                continue
            if l[0] == "CURRICULA:":
                flag_rooms = False
                flag_curricula = True
                continue
            if l[0] == "UNAVAILABILITY_CONSTRAINTS:":
                flag_curricula = False
                flag_unavai = True
                continue
            if l[0] == "END.":
                break    
            
            if flag_info:
                info.append(l[-1])
            if flag_courses:
                courses[l[0]] = Course(l[1], int(l[2]), int(l[3]), int(l[4])) 
            if flag_rooms:
                rooms[l[0]] = Room(l[-1])
            if flag_curricula:
                c = []
                for i in range(int(l[1])):
                    c.append(l[2 + i])
                curricula[l[0]] = Curriculum(l[1], c)
            if flag_unavai:
                const = Unavailability(l[0], l[1], l[2])
                unavailabilyties.append(const)

    instance = Instance(
        info[0],
        int(info[1]),
        int(info[2]),
        int(info[3]),
        int(info[4]),
        int(info[5]),
        int(info[6]),
        courses=courses,
        rooms=rooms,
        curricula=curricula,
        unavailabilyties=unavailabilyties)
    
    return instance



if __name__ == "__main__":
    print(parse_ctt("toy.txt"))