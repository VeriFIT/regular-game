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
    title="Tutorial 1",
    text="Heslo musí mít délku alespoň osm znaků a musí obsahovat alespoň jedno malé písmeno anglické abecedy, jedno velké písmeno anglické abecedy, jednu číslici a musí to být palindrom (tj. čte se zepředu stejně jako zezadu).",
    conditions = [
        ("délka alespoň osm znaků", "(assert (<= 8 (str.len result)))"),
        ("alespoň jedno malé písmeno anglické abecedy", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"a\" \"z\")) re.all)))"),
        ("alespoň jedno velké písmeno anglické abecedy", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"A\" \"Z\")) re.all)))"),
        ("alespoň jedno arabská číslice", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"0\" \"9\")) re.all)))"),
        ("palindrom", "(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (div (str.len result) 2))) (= (str.at result i) (str.at result (- (- (str.len result) i) 1))))))"),
    ]
)
