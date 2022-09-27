#!/usr/bin/env python3

import os
os.environ.setdefault('DJANGO_SETTINGS_MODULE','regular_game_site.settings')

import django
django.setup()

from regular_game.models import Task, Snippet

############################### TASK 1 ##########################################
task = Task(
            num=1,
            title="ahoj",
            text="tady ma byt text",
           )
task.save()

# examples
task.snippet_set.create(snip_type='Y',
                        text="bagr")
task.snippet_set.create(snip_type='Y',
                        text="bagříčekříčekříčekříčekříček")

task.snippet_set.create(snip_type='N',
                        text="traktor")
task.snippet_set.create(snip_type='N',
                        text="hárvestr")

############################### TASK 2 ##########################################

task = Task(
            num=2,
            title="Andrej",
            text="Za Andreje bilo lýp",
           )
task.save()

# examples
task.snippet_set.create(snip_type='Y',
                        text="Andrej sedí za mřížemi")
task.snippet_set.create(snip_type='Y',
                        text="tunelujeme eurodotace")

task.snippet_set.create(snip_type='N',
                        text="řepka mňam mňam")
task.snippet_set.create(snip_type='N',
                        text="agrofert mudlofert ")

############################### TASK 3 ##########################################
