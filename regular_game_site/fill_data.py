#!/usr/bin/env python3

import os
os.environ.setdefault('DJANGO_SETTINGS_MODULE','regular_game_site.settings')

import django
django.setup()

from regular_game.models import Task, Snippet


############################### TASK 1 ##########################################
task = Task(
    num=1,
    title="E-maily",
    text="Zhosti se úlohy programátora nástroje pro detekci spamu a nalezni regex pro podezřelý text v emailech.",
)
task.save()

# examples
task.snippet_set.create(
    snip_type='Y',
    text="For your knowledge, 25%% of this fund $25,000,000 USD will be given to you."
)
task.snippet_set.create(
    snip_type='Y',
    text="It is the sum of $7,000,000 USD (SEVEN MILLION UNITED STATES DOLLARS) cash."
)
task.snippet_set.create(
    snip_type='Y',
    text="I am writing you to seek your assistance to transfer our cash of ($12,000,000 USD)."
)

task.snippet_set.create(
    snip_type='N',
    text="The company said it would post a net loss of 23 million euros ($23 million)."
)
task.snippet_set.create(
    snip_type='N',
    text="*Proprietary auto routing technology | *$9.99 commission"
)


############################### TASK 2 ##########################################
task = Task(
    num=2,
    title="Soukromé zprávy",
    text="Najdi způsob, jak označit všechny zprávy v první konverzaci.",
)
task.save()

# examples
task.snippet_set.create(
    snip_type='Y',
    text="Hello cindy, running late I've been stopped by a train :)"
)
task.snippet_set.create(
    snip_type='Y',
    text="Ok. :)"
)
task.snippet_set.create(
    snip_type='Y',
    text="How much do i owe you. Not sure what tickets cost these days. :)"
)
task.snippet_set.create(
    snip_type='Y',
    text="Ten bucks, I think :)"
)

task.snippet_set.create(
    snip_type='N',
    text="Hope u guys made it home okay. Had fun hanging out, hope u had a good bday"
)
task.snippet_set.create(
    snip_type='N',
    text="Yup got home a couple hours ago. Very fun bday, thanks!"
)
task.snippet_set.create(
    snip_type='N',
    text="Good :) look forward to hanging out soon."
)
task.snippet_set.create(
    snip_type='N',
    text="U2!"
)


############################### TASK 3 ##########################################
task = Task(
    num=3,
    title="E-maily 2",
    text="Nová várka emailů bude potřebovat pokročilejší detekci podezřelých finančních obnosů.",
)
task.save()

# examples
task.snippet_set.create(
    snip_type='Y',
    text="For your knowledge, 25%% of this fund $25,000,000.00 will be given to you."
)
task.snippet_set.create(
    snip_type='Y',
    text="It is the sum of US$27,000,000.00 (TWENTY SEVEN MILLION UNITED STATES DOLLARS) cash."
)
task.snippet_set.create(
    snip_type='Y',
    text="I am writing you to seek your assistance to transfer our cash of ($12,000,000.00)."
)

task.snippet_set.create(
    snip_type='N',
    text="The company said it would post a net loss of 23 million euros ($23 million)."
)
task.snippet_set.create(
    snip_type='N',
    text="License: Free to try; $1,000.00 to buy"
)
task.snippet_set.create(
    snip_type='N',
    text="*Proprietary auto routing technology | *$9.99 commission"
)


############################### TASK 4 ##########################################
task = Task(
    num=4,
    title="Propagační tweety",
    text="Pro svůj výzkum potřebuješ dataset propagačních tweetů z Twitteru. Najdi regex, který je korektně detekuje.",
)
task.save()

# examples
task.snippet_set.create(
    snip_type='Y',
    text="RT @4EverMaheshFan: Just came out of the #AvengersEndgame premiere!! I'm at a lost for words!!"
)
task.snippet_set.create(
    snip_type='Y',
    text="@mikefish  Fair enough. But i have the #Kindle2 and I think it's perfect."
)
task.snippet_set.create(
    snip_type='Y',
    text="BIG NEWS Just got a sneak peak at a new #iPhone promo poster."
)
task.snippet_set.create(
    snip_type='Y',
    text="HTML 5 Demos! Lots of great stuff to come! Yes, I'm excited. #googleio"
)

task.snippet_set.create(
    snip_type='N',
    text="Beginning JavaScript and CSS Development with jQuery #javascript #css #jquery"
)
task.snippet_set.create(
    snip_type='N',
    text="@stevethegoose We had one in your honor while watching the Avengers."
)
task.snippet_set.create(
    snip_type='N',
    text="Even for researchers the information provided is less than you can get from #google or #wikipedia"
)
task.snippet_set.create(
    snip_type='N',
    text="#lebron best athlete of our generation, if not all time (basketball related)"
)


############################### TASK 5 ##########################################
task = Task(
    num=5,
    title="Sledování investic",
    text="Jakožto velkého investora tě nezajímají drobné nákupy a prodeje akcií ve tvém portfoliu. Najdi regex pro detekci drobných nákupů a prodejů, abys je mohl vyfiltrovat.",
)
task.save()

# examples
task.snippet_set.create(
    snip_type='Y',
    text="2021-07-29 15:37:09;BAC;sell;36.67;USD"
)
task.snippet_set.create(
    snip_type='Y',
    text="2021-07-29 21:34:04;JPM;buy;135.78;USD"
)
task.snippet_set.create(
    snip_type='Y',
    text="2021-09-27 23:00:04;AVGO;buy;278.13;USD"
)
task.snippet_set.create(
    snip_type='Y',
    text="2021-08-29 11:34:20;ADBE;sell;336.99;USD"
)
task.snippet_set.create(
    snip_type='Y',
    text="2021-09-29 11:20:00;HD;buy;286.18;USD"
)
task.snippet_set.create(
    snip_type='Y',
    text="2021-07-27 03:11:15;TMO;buy;483.88;USD"
)
task.snippet_set.create(
    snip_type='Y',
    text="2021-07-27 02:11:52;KO;buy;49.81;USD"
)
task.snippet_set.create(
    snip_type='Y',
    text="2021-09-28 03:17:53;INTC;sell;45.38;USD"
)

task.snippet_set.create(
    snip_type='N',
    text="2021-07-29 17:52:07;AMZN;buy;3187.55;USD"
)
task.snippet_set.create(
    snip_type='N',
    text="2021-07-29 23:05:42;BAC;buy;1990.04;USD"
)
task.snippet_set.create(
    snip_type='N',
    text="2021-07-29 16:48:19;GOOGL;sell;2137.44;USD"
)
task.snippet_set.create(
    snip_type='N',
    text="2021-09-28 01:10:50;SHOP;buy;1342.40;USD"
)
task.snippet_set.create(
    snip_type='N',
    text="2021-09-28 12:23:35;ADBE;buy;838.10;USD"
)
task.snippet_set.create(
    snip_type='N',
    text="2021-09-28 17:21:24;JNJ;sell;1173.14;USD"
)
task.snippet_set.create(
    snip_type='N',
    text="2021-09-27 16:07:35;BHP;sell;982.49;USD"
)
task.snippet_set.create(
    snip_type='N',
    text="2021-09-27 16:11:45;NVDA;buy;555.29;USD"
)
task.snippet_set.create(
    snip_type='N',
    text="2021-09-27 09:00:39;TSLA;buy;772.87;USD"
)


############################### TASK 6 ##########################################
task = Task(
    num=6,
    title="Logy webového serveru",
    text="Takto běžně vypadají zprávy, které monitorují stav běžícího webového serveru. Vžij se do role systémového administrátora a najdi regex popisující to, co mají společného všechny zprávy z první skupiny.",
)
task.save()

# examples
task.snippet_set.create(
    snip_type='Y',
    text='66.249.66.47 - - [10/Feb/2019:20:56:04 +0100] "GET /robots.txt HTTP/1.1" 404 3798 "-" "Mozilla/5.0 (compatible; Googlebot/2.1)"'
)
task.snippet_set.create(
    snip_type='Y',
    text='46.17.47.173 - - [09/Feb/2019:08:41:01 +0100] "GET /recordings/ HTTP/1.1" 404 3779 "-" "python-requests/2.20.1"'
)
task.snippet_set.create(
    snip_type='Y',
    text='80.82.77.33 - - [08/Feb/2019:09:21:51 +0100] "GET /sitemap.xml HTTP/1.1" 404 3728 "-" "-"'
)
task.snippet_set.create(
    snip_type='Y',
    text='157.55.39.34 - - [18/Feb/2019:03:23:07 +0100] "GET /robots.txt HTTP/1.1" 404 3770 "-" "Mozilla/5.0 (compatible; bingbot/2.0)"'
)

task.snippet_set.create(
    snip_type='N',
    text='2001:67c:1220:80c:d4:985a:df2c:d717 - - [13/Feb/2019:07:49:01 +0100] "GET / HTTP/1.1" 200 58341 "-" "curl/7.61.1"'
)
task.snippet_set.create(
    snip_type='N',
    text='198.27.69.191 - - [08/Feb/2019:09:45:38 +0100] "GET / HTTP/1.1" 200 24041 "-" "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:64.0) Gecko/20100101 Firefox/64.0"'
)
task.snippet_set.create(
    snip_type='N',
    text='157.55.39.35 - - [20/Feb/2019:13:00:36 +0100] "GET /robots.txt HTTP/1.1" 200 3786 "-" "Mozilla/5.0 (compatible; bingbot/2.0; 404 )"'
)
task.snippet_set.create(
    snip_type='N',
    text='46.229.168.140 - - [10/Feb/2019:16:04:45 +0100] "POST /robots.txt HTTP/1.1" 404 3761 "-" "Mozilla/5.0 (compatible; SemrushBot/3~bl;)"'
)