#!/usr/bin/env python3

import os
os.environ.setdefault('DJANGO_SETTINGS_MODULE','regular_game_site.settings')

import django
django.setup()

from regular_game.models import Task, Snippet

num = 1

def create_task(title, text, pos_snip, neg_snip):
    global num
    task = Task(
        num=num,
        title=title,
        text=text)
    task.save()
    num += 1

    for snip in pos_snip:
        task.snippet_set.create(snip_type='Y', text=snip)
    for snip in neg_snip:
        task.snippet_set.create(snip_type='N', text=snip)


############################### TUTORIAL ########################################
create_task(
    title="Tutorial 1",
    text="Před tím, než Tě pustíme na Gargamela, musíš projít krátkým tréninkem.  Napiš regex, který zachytí všechny řádky vlevo a propustí všechny řádky vpravo.  Nápovědu, jak psát regexy, můžeš najít níže.  Tady Ti můžou pomoci operátory \"<tt>|</tt>\" a \"<tt>[</tt>, <tt>]</tt>\". Nezapomeň, že čím kratší regex vytvoříš, tím lepší skóre budeš mít!",
    pos_snip=["aa1bb", "aa2bb", "aa3bb"],
    neg_snip=["aaXbb", "aaAbb", "aabb"]
)

create_task(
    title="Tutorial 2",
    text="Další jednoduchý úkol.  Tady můžeš zkusit najít podřetězec který je na všech řádcích vlevo a není na žádném řádku vpravo.",
    pos_snip=["dkjfl_abc_kldjfals", "jkdlajfl_abc_adrjfkal", "uiks34_abc_ffm"],
    neg_snip=["abababababababab", "abbcabbc_abbcabbca", "jkjlkfkladjlvd", "dkfjalskvjlckjnaiejf94rasd3"]
)

create_task(
    title="Tutorial 3",
    text="Jak vyřešíš tento úkol?  Tady se Ti může hodit konstrukce <tt>.*</tt>, která zachytí libovolný řetězec.",
    pos_snip=["XaaaaaaaaaaaaaaaaaaX", "YaaaaaaaaaaaaaaaaaaaaaaaaY"],
    neg_snip=["XaaaaaaaaaaaaaaaaaaY", "YaaaaaaaaaaaaaaaaaaaaaaaaX"]
)

create_task(
    title="Tutorial 4",
    text="U tohoto úkolu se Ti můžou hodit konstrukce \"<tt>[</tt>\", \"<tt>]</tt>\" pro množinu symbolů a \"<tt>{</tt>\", \"<tt>}</tt>\" pro počet opakování.",
    pos_snip=["12345", "84579", "12783", "45178", "34791"],
    neg_snip=["12a43", "a3452", "7b823", "234k3", "2422a", "5423"]
)

create_task(
    title="Tutorial 5",
    text="Tady se Ti můžou hodit tzv. kotvy \"<tt>^</tt>\" a \"<tt>$</tt>\", kterými se můžeš odkázat na začátek a konec řádku.",
    pos_snip=["12345", "12314", "12783", "20954", "33904"],
    neg_snip=["22143", "43452", "70821", "23478", "24220"]
)


############################### TASK 1 ##########################################
create_task(
    title="Detekce spamu",
    text="A teď už Tě pustíme do boje s Gargamelem!  Gargamel se pokouší zahltit Internet spamem.  Zabraň mu v tom a vytvoř regex, který odhalí spamové zprávy a zahodí je do koše!",
    pos_snip=[
        "For your knowledge, 25% of this fund $25,000,000 USD will be given to you.",
        "It is the sum of $7,000,000 USD (SEVEN MILLION UNITED STATES DOLLARS) cash.",
        "I am writing you to seek your assistance to transfer our cash of ($12,000,000 USD)."
        ],
    neg_snip=[
        "The company said it would post a net loss of 23 million euros (US$23 million).",
        "*Proprietary auto routing technology | *$9.99 commission"
        ]
)


############################### TASK 2 ##########################################
create_task(
    title="Soukromé zprávy",
    text="Pozor, Gargamel se snaží dostat k soukromým zprávám Tvojí mámy!  Zabraň mu v tom!",
    pos_snip=[
        "Hello cindy, running late I've been stopped by a train :).",
        "Ok. :)",
        "How much do i owe you. Not sure what tickets cost these days. :)",
        "Ten bucks, I think :)"
        ],
    neg_snip=[
        "Hope u guys made it home okay. Had fun hanging out, hope u had a good bday",
        "Yup got home a couple hours ago. Very fun bday, thanks!",
        "Good :) look forward to hanging out soon.",
        "U2!"
        ]
)

############################### TASK 3 ##########################################
create_task(
    title="Pokročilá detekce spamu",
    text="Gargamel vylepšil svou technologii pro generování spamu.  Srovnej s ním krok a odhal všechen spam!",
    pos_snip=[
        "For your knowledge, 25% of this fund $25,000,000.00 will be given to you.",
        "It is the sum of US$27,000,000.00 (TWENTY SEVEN MILLION UNITED STATES DOLLARS) cash.",
        "I am writing you to seek your assistance to transfer our cash of ($12,000,000)."
        ],
    neg_snip=[
        "The company said it would post a net loss of 23 million euros (US$23 million).",
        "License: Free to try; $100,000.00 to buy",
        "*Proprietary auto routing technology | *$9.00 commission"
        ]
)

############################### TASK 4 ##########################################
create_task(
    title="Falešné tweety",
    text="Gargamel se snaží pomocí lživých tweetů obelstít veřejnost.  Najdi regex, který je správně detekuje.",
    # text="Pro svůj výzkum potřebuješ dataset propagačních tweetů z Twitteru. Najdi regex, který je korektně detekuje.",
    pos_snip=[
        "RT @4EverMahesh: Just came out of the #AvengersEndgame premiere!! I'm at a lost for words!!",
        "@mikefish  Fair enough. But i have the #Kindle2 and I think it's perfect.",
        "BIG NEWS Just got a sneak peak at a new #iPhone promo poster.",
        "HTML 5 Demos! Lots of great stuff to come! Yyeess, I'm excited. #googleio"
        ],
    neg_snip=[
        "Beginning JavaScript and CSS Development with jQuery Today #javascript #css #jquery",
        "@stevethegoose I had one in your honor while watching the Avengers.",
        "Even for researchers the information provided is less than you can get from #google or #wikipedia",
        "#lebron best athlete of our generation, if not all time (basketball related)"
        ]
)


############################### TASK 5 ##########################################
create_task(
    title="Útok na burzu",
    text="Kontaktoval Tě hlavní bezpečnostní technik New Yorkské burzy:  Gargamel se snaží zmanipulovat trh a nakoupit velké množství akcií.  Napiš regex, který na burzu pošle jen legitimní obchody!",
    pos_snip=[
        "2021-07-29 15:37:09;BAC;sell;36.67;USD",
        "2021-07-29 21:34:04;JPM;buy;135.78;USD",
        "2021-09-27 23:00:04;AVGO;buy;278.13;USD",
        "2021-08-29 11:34:20;ADBE;sell;336.99;USD",
        "2021-09-29 11:20:00;HD;buy;286.18;USD",
        "2021-07-27 03:11:15;TMO;buy;483.88;USD",
        "2021-07-27 02:11:52;KO;buy;49.81;USD",
        "2021-09-28 03:17:53;INTC;sell;45.38;USD"
        ],
    neg_snip=[
        "2021-07-29 17:52:07;AMZN;buy;3187.55;USD",
        "2021-07-29 23:05:42;BAC;buy;1990.04;USD",
        "2021-07-29 16:48:19;GOOGL;sell;2137.44;USD",
        "2021-09-28 01:10:50;SHOP;buy;1342.40;USD",
        "2021-09-28 12:23:35;ADBE;buy;838.10;USD",
        "2021-09-28 17:21:24;JNJ;sell;1173.14;USD",
        "2021-09-27 16:07:35;BHP;sell;982.49;USD",
        "2021-09-27 16:11:45;NVDA;buy;555.29;USD",
        "2021-09-27 09:00:39;TSLA;buy;772.87;USD"
        ]
)


############################### TASK 6 ##########################################
create_task(
    title="Zachraň lidstvo před jadernou katastrofou!",
    text="Pozor!  Gargamel tvrdí, že se dostal do řídicího systému jedné jaderné elektrárny a hrozí, že způsobí roztavení reaktoru a jadernou katastrofu.  Napiš regex, který ze serverových logů odhalí, do které elektrárny se dostal, ať Gargamel může být dopaden!",
    pos_snip=[
        '66.249.66.47 - - [10/Feb/2019:20:56:04 +0100] "GET /robots.txt HTTP/1.1" 404 3798 "-" "Mozilla/5.0 (compatible; Googlebot/2.1)"',
        '46.17.47.173 - - [09/Feb/2019:08:41:01 +0100] "GET /recordings/ HTTP/1.1" 404 3779 "-" "python-requests/2.20.1"',
        '80.82.77.33 - - [08/Feb/2019:09:21:51 +0100] "GET /sitemap.xml HTTP/1.1" 404 3728 "-" "-"',
        '157.55.39.34 - - [18/Feb/2019:03:23:07 +0100] "GET /robots.txt HTTP/1.1" 404 3770 "-" "Mozilla/5.0 (compatible; bingbot/2.0)"'
        ],
    neg_snip=[
        '2001:67c:1220:80c:d4:985a:df2c:d717 - - [13/Feb/2019:07:49:01 +0100] "GET / HTTP/1.1" 200 57741 "-" "curl/7.61.1"',
        '66.249.82.47 - - [08/Feb/2019:09:45:38 +0100] "GET / HTTP/1.1" 200 24041 "-" "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:64.0) Gecko/20100101 Firefox/64.0"',
        '46.17.33.173 - - [20/Feb/2019:23:56:36 +0100] "GET /robots.txt HTTP/1.1" 200 2151 "-" "Mozilla/5.0 (compatible; bingbot/2.0; 404 )"',
        '157.55.39.34 - - [10/Feb/2019:16:04:45 +0100] "POST /robots.txt HTTP/1.1" 404 3703 "-" "Mozilla/5.0 (compatible; SemrushBot/3~bl;)"'
        ]
)
