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



############################### TUTORIAL ########################################
create_task(
    title="Tutorial 1",
    text="Heslo musí obsahovat řetězec \"VeriFIT\" a navíc jeho první dva znaky musí odpovídat posledním dvěma znakům.",
    conditions = [
        ("musí obsahovat řetězec \"VeriFIT\"", "(assert (str.contains result \"VeriFIT\"))"),
        ("první dva znaky musí odpovídat posledním dvěma znakům", "(assert (= (str.substr result 0 2) (str.substr result (- (str.len result) 2) 2)))"),
    ]
)

