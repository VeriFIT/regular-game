#!/usr/bin/env python3

import os
os.environ.setdefault('DJANGO_SETTINGS_MODULE','regular_game_site.settings')

import django
django.setup()

from game23.models import Task

num = 1

def create_task(title, text):
    global num
    task = Task(
        num=num,
        title=title,
        text=text)
    task.save()
    num += 1


############################### TUTORIAL ########################################
create_task(
    title="Tutorial 1",
    text="Před tím, než Tě pustíme na Gargamela, musíš projít krátkým tréninkem.  Napiš regex, který zachytí všechny řádky vlevo a propustí všechny řádky vpravo.  Nápovědu, jak psát regexy, můžeš najít níže.  Tady Ti můžou pomoci operátory \"<tt>|</tt>\" a \"<tt>[</tt>, <tt>]</tt>\". Nezapomeň, že čím kratší regex vytvoříš, tím lepší skóre budeš mít!"
)

