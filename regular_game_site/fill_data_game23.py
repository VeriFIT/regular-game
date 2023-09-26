#!/usr/bin/env python3

import os
os.environ.setdefault('DJANGO_SETTINGS_MODULE','regular_game_site.settings')

import django
django.setup()

from game23.models import Task, Condition

num = 1

def create_task(title, text, conditions):
    global num
    task = Task(
        num=num,
        title=title,
        text=text)
    task.save()
    num += 1

    for (text, smt) in conditions:
        task.condition_set.create(text=text, smt=smt)


# clean
Task.objects.all().delete()

############################### TUTORIAL ########################################
create_task(
    title="Tutorial 1",
    text="Heslo musí obsahovat řetězec \"VeriFIT\" a navíc jeho první dva znaky musí odpovídat posledním dvěma znakům.",
    conditions = [
        ("musí obsahovat řetězec \"VeriFIT\"", "(assert (str.contains result \"VeriFIT\"))"),
        ("první dva znaky musí odpovídat posledním dvěma znakům", "(assert (= (str.substr result 0 2) (str.substr result (- (str.len result) 2) 2)))"),
    ]
)

create_task(
    title="Tutorial 2",
    text="Heslo musí mít délku alespoň osm znaků a musí obsahovat alespoň jedno malé písmeno anglické abecedy, jedno velké písmeno anglické abecedy, jednu číslici a musí to být palindrom (tj. čte se zepředu stejně jako zezadu).",
    conditions = [
        ("délka alespoň osm znaků", "(assert (<= 8 (str.len result)))"),
        ("alespoň jedno malé písmeno anglické abecedy", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"a\" \"z\")) re.all)))"),
        ("alespoň jedno velké písmeno anglické abecedy", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"A\" \"Z\")) re.all)))"),
        ("alespoň jedno arabská číslice", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"0\" \"9\")) re.all)))"),
        ("palindrom", "(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (div (str.len result) 2))) (= (str.at result i) (str.at result (- (- (str.len result) i) 1))))))"),
    ]
)

# NOTE: We cannot allow non-constant number of digits in the password or z3 times out
fpc_formula = '''
(assert (or (exists ((x0 Int) (x1 Int) (x2 Int) (x3 Int) (x4 Int)) (and (<= 0 x0) (< x0 (str.len result)) (str.is_digit (str.at result x0)) (<= 0 x1) (< x1 (str.len result)) (str.is_digit (str.at result x1)) (<= 0 x2) (< x2 (str.len result)) (str.is_digit (str.at result x2)) (<= 0 x3) (< x3 (str.len result)) (str.is_digit (str.at result x3)) (<= 0 x4) (< x4 (str.len result)) (str.is_digit (str.at result x4)) (= (+ (str.to_int (str.at result x0)) (str.to_int (str.at result x1)) (str.to_int (str.at result x2)) (str.to_int (str.at result x3)) (str.to_int (str.at result x4))) 23) (not (exists ((x5 Int)) (and (not (= x0 x5)) (not (= x1 x5)) (not (= x2 x5)) (not (= x3 x5)) (not (= x4 x5)) (str.is_digit (str.at result x5)))))))))
'''

create_task(
    title="Heslo pro nejvyššího bankéře",
    # text="The password must contain 5 digits that add up to the largest sum of money that cannot be obtained when having an (infinite) number of 5 czk and 7 czk coins (e.g. 13 czk cannot be obtained).",
    text="Heslo musí obsahovat 5 číslic, které dávají dohromady nejvyšší částku peněz, kterou nelze získat při (nekonečném) počtu mincí 5 Kč a 7 Kč (např. nelze získat 13 Kč).",
    conditions = [
        (
            "Heslo musí obsahovat 5 číslic, které dávají dohromady nejvyšší částku peněz, kterou nelze získat při (nekonečném) počtu mincí 5 Kč a 7 Kč (např. nelze získat 13 Kč).",
            fpc_formula  # Explicit formula for FCP: a*b - a - b ~= 5*7 - 5 - 7 = 35 - 12 = 23
        ),
    ]
)
