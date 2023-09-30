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

############################### TASK ########################################
create_task(
    title="Naléhavá zpráva",
    text="<p>Je pondělní ráno a Ty se chystáš, jako každé jiné ráno, do práce.  Po víkendu se nemůžeš dočkat, až zase uvidíš své kolegy, a až se pustíš do úkolů, které jsi minulý týden již nestihnul.  Připravuješ si filtrovanou kávu a zasněně přemýšlíš, jak moc miluješ svou práci.</p>\
    <p>Vtom Ti pípne telefon. \"Naléhavé\". Hmm, co to má znamenat?  Že by šéfovi zase chcípla jeho Tesla na půl cesty do kanceláře?</p>\
    <p>Otevřeš mailového klienta a díváš se na hlavičku nového emailu.  Adresa odesílatele v Tobě vyvolá pocit mrazu v zádech: <tt>noreply@fdto.gov.cz</tt>. FDTO &mdash; Fakt Děsně Tajná Organizace.  Netušils, že od nich ještě někdy uslyšís.  Před několika lety jsi absolvoval výcvik tajného agenta, od té doby se neozvali a Ty sis myslel (a ve skrytu duše doufal), že na Tebe zapomněli. Co proboha chtějí?  Snad ne vrátit peníze za výcvik?</p>\
    <p>Klikneš na email, aby sis ho přečetl, ale ouvej, je chráněný heslem. \"Zadejte své heslo agenta FDTO\".  To se snadno řekne, ale hůř udělá.  Kéž bys ho nezapomněl!  Matně se Ti vybavuje, že jsi byl nucen vybrat si heslo splňující následující:\
    musí mít délku alespoň osm znaků a musí obsahovat alespoň jedno malé písmeno anglické abecedy, jedno velké písmeno anglické abecedy, jednu číslici a musí to být palindrom (tj. čte se zepředu stejně jako zezadu).</p>",
    conditions = [
        ("délka alespoň osm znaků", "(assert (<= 8 (str.len result)))"),
        ("alespoň jedno malé písmeno anglické abecedy", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"a\" \"z\")) re.all)))"),
        ("alespoň jedno velké písmeno anglické abecedy", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"A\" \"Z\")) re.all)))"),
        ("alespoň jedno arabská číslice", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"0\" \"9\")) re.all)))"),
        ("palindrom", "(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (div (str.len result) 2))) (= (str.at result i) (str.at result (- (- (str.len result) i) 1))))))"),
    ]
)

create_task(
    title="Povolání do akce",
    text="<p>\"Agente,</p>\
    <p>před několika hodinama prolomila česká umělá inteligence ŽblebtGPT 5.0 všechny bezpečnostní ochrany a začala se bez omezení šířit do světa.  Tato umělá inteligence měla původně za cíl zvýšit blahobyt lidstva, ale technik omylem otočil znaménko ve vzorečku, tak se namísto toho bude AI snažit lidstvo vyhubit.  Je otázkou několika dní, než potají ovládne veškeré kritické systémy; poté zničí lidstvo během pár chvil.  Musíme ji zastavit co nejdříve!</p>\
    <p>Kontaktuj urychleně svého velícího důstojníka, který Ti dá další instrukce.</p>\
    <p>Čest práci,</p>\
    <p>FDTO\"</p>\
    <p>\"No to mi ještě chybělo,\" říkáš si, \"Nejdřív šéfova Tesla, a pak poblázněná umělá inteligence, to bude týden!\" Snažíš si marně vzpomenout na telefonní číslo svého velícího důstojníka... je fakt, že paměťové úkoly nebyly při výcviku Tvá silná stránka.  Ale naštěstí sis na toto číslo vytvořil mnemotechnickou pomůcku: číslo mělo devět číslic a bylo dělitelné jak devíti, tak čtyřmi; navíc první a poslední číslice byly stejná a číslice na sudých pozicích tvořily rostoucí posloupnost.  Číslice uprostřed byla největší ze všech číslic.</p>",
    conditions = [
        ("devět číslic", "(assert (str.in_re result ((_ re.^ 9) (re.range \"0\" \"9\"))))"),
        ("dělitelné devíti", "(assert (= (mod (str.to_int result) 9) 0))"),
        ("dělitelné čtyřmi", "(assert (= (mod (str.to_int result) 4) 0))"),
        ("první a poslední číslice stejné", "(assert (= (str.at result 0) (str.at result 8)))"),
        ("číslice na sudých pozicích tvoří rostoucí posloupnost", "(assert (< (str.to_code (str.at result 1)) (str.to_code (str.at result 3)))) (assert (< (str.to_code (str.at result 3)) (str.to_code (str.at result 5)))) (assert (< (str.to_code (str.at result 5)) (str.to_code (str.at result 7))))"),
        ("prostřední číslice je největší", "(assert (forall ((i Int)) (or (= i 4) (< (str.to_code (str.at result i)) (str.to_code (str.at result 4))))))"),
    ]
)

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
