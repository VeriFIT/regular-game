#!/usr/bin/env python3

import os
os.environ.setdefault('DJANGO_SETTINGS_MODULE','regular_game_site.settings')

import django
from django.db import IntegrityError
django.setup()

from game23.models import Task, Condition, Difficulty

num = 1

def create_task(title, text, conditions):
    global num
    task = Task(
        num=num,
        title=title,
        text=text)
    task.save()
    num += 1

    for difficulty, text, smt in conditions:
        task.condition_set.create(text=text, smt=smt, difficulty=Difficulty.objects.get(order=difficulty))


def save_difficulty(difficulty):
    try:
        difficulty.save()
    except IntegrityError as _:
        pass


############################### DIFFICULTY ########################################

easy = Difficulty(
    name="Jednoduchá",
    order=1,
    avatar="Pikaču",
    avatar_url="https://c.tenor.com/tZVpbfTIjNMAAAAM/pikachu.gif",
    task_ok_score=20,
    task_fail_score=0,
    task_skip_score=0
)
medium = Difficulty(
    name="Normální",
    order=2,
    avatar="Doom Slayer",
    avatar_url="https://media.tenor.com/enYPjlc7Xk8AAAAd/doom.gif",
    task_ok_score=40,
    task_fail_score=-10,
    task_skip_score=-20
)

hard = Difficulty(
    name="Těžká",
    order=3,
    avatar="Hackerman",
    avatar_url="https://media0.giphy.com/media/3knKct3fGqxhK/giphy.gif",
    task_ok_score=60,
    task_fail_score=-20,
    task_skip_score=-60
)
save_difficulty(easy)
save_difficulty(medium)
save_difficulty(hard)


# clean
Task.objects.all().delete()

############################### TASK ########################################
create_task(
    title="Naléhavá zpráva",
    text="<p>Je pondělní ráno a Ty se chystáš, jako každé jiné ráno, do práce.  Po víkendu se nemůžeš dočkat, až zase uvidíš své kolegy, a až se pustíš do úkolů, které jsi minulý týden již nestihnul.  Připravuješ si filtrovanou kávu a zasněně přemýšlíš, jak moc miluješ svou práci.</p>\
    <p>Vtom Ti pípne telefon. \"Naléhavé\". Hmm, co to má znamenat?  Že by šéfovi zase chcípla jeho Tesla na půl cesty do kanceláře?</p>\
    <p>Otevřeš mailového klienta a díváš se na hlavičku nového emailu.  Adresa odesílatele v Tobě vyvolá pocit mrazu v zádech: <tt>noreply@fdto.gov.cz</tt>. FDTO &mdash; Fakt Děsně Tajná Organizace.  Netušils, že od nich ještě někdy uslyšís.  Před několika lety jsi absolvoval výcvik tajného agenta, od té doby se neozvali a Ty sis myslel (a ve skrytu duše doufal), že na Tebe zapomněli. Co proboha chtějí?  Snad ne vrátit peníze za výcvik?</p>\
    <p>Klikneš na email, aby sis ho přečetl, ale ouvej, je chráněný heslem. \"Zadejte své heslo agenta FDTO\".  To se snadno řekne, ale hůř udělá.  Kéž bys ho nezapomněl!  Matně se Ti vybavuje, že jsi byl nucen vybrat si heslo splňující následující:</p>",
    conditions = [
        (easy.order, "Heslo musí mít alespoň osm znaků.", "(assert (<= 8 (str.len result)))"),
        (easy.order, "Heslo musí obsahovat alespoň jedno malé písmeno anglické abecedy.", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"a\" \"z\")) re.all)))"),
        (easy.order, "Heslo musí obsahovat alespoň jedno velké písmeno anglické abecedy.", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"A\" \"Z\")) re.all)))"),
        (medium.order, "Heslo musí obsahovat alespoň jednu arabskou číslici.", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"0\" \"9\")) re.all)))"),
        (hard.order, "Heslo musí být palindrom (tj. čte se zepředu stejně jako zezadu).", "(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (div (str.len result) 2))) (= (str.at result i) (str.at result (- (- (str.len result) i) 1))))))"),
    ]
)

create_task(
    title="Povolání do akce",
    text="<p>\"Agente,</p>\
    <p>před několika hodinama prolomila česká umělá inteligence ŽblebtGPT 5.0 všechny bezpečnostní ochrany a začala se bez omezení šířit do světa.  Tato umělá inteligence měla původně za cíl zvýšit blahobyt lidstva, ale technik omylem otočil znaménko ve vzorečku, tak se namísto toho bude AI snažit lidstvo vyhubit.  Je otázkou několika dní, než potají ovládne veškeré kritické systémy; poté zničí lidstvo během pár chvil.  Musíme ji zastavit co nejdříve!</p>\
    <p>Kontaktuj urychleně svého velícího důstojníka, který Ti dá další instrukce.</p>\
    <p>Čest práci,</p>\
    <p>FDTO\"</p>\
    <p>\"No to mi ještě chybělo,\" říkáš si, \"Nejdřív šéfova Tesla, a pak poblázněná umělá inteligence, to bude týden!\" Snažíš si marně vzpomenout na telefonní číslo svého velícího důstojníka... je fakt, že paměťové úkoly nebyly při výcviku Tvá silná stránka.  Ale naštěstí sis na toto číslo vytvořil mnemotechnickou pomůcku:</p>",
    conditions = [
        (easy.order, "Číslo mělo devět číslic.", "(assert (str.in_re result ((_ re.^ 9) (re.range \"0\" \"9\"))))"),
        (easy.order, "Číslo bylo dělitelné čtyřmi.", "(assert (= (mod (str.to_int result) 4) 0))"),
        (easy.order, "První a poslední číslice byly stejné.", "(assert (= (str.at result 0) (str.at result 8)))"),
        (easy.order, "Prostřední číslice byla největší.", "(assert (forall ((i Int)) (or (= i 4) (< (str.to_code (str.at result i)) (str.to_code (str.at result 4))))))"),
        (medium.order, "Číslice na sudých pozicích tvořily rostoucí posloupnost.", "(assert (< (str.to_code (str.at result 1)) (str.to_code (str.at result 3)))) (assert (< (str.to_code (str.at result 3)) (str.to_code (str.at result 5)))) (assert (< (str.to_code (str.at result 5)) (str.to_code (str.at result 7))))"),
        (hard.order, "Číslo bylo dělitelné i devíti.", "(assert (= (mod (str.to_int result) 9) 0))"),
    ]
)

create_task(
    title="Telefonát",
    text="<p>Vytočil jsi na telefonu číslo svého velícího důstojníka...</p>\
        <p>\"Volané číslo neexistuje.  Prosíme, ověřte si, že voláte správné číslo.\"</p>\
        <p>No tak ani s pamětí na mnemotechnické pomůcky to nebylo žádná sláva.  Asi Ti nezbývá, než sednout na čopra a jet na velitelsví osobně.  Ukousnul sis poslední sousto z toustu, dopil kávu (AI apokalypsa počká), hodil na sebe bundu a vyběhl z bytu, rovnou do výtahu.  Zavřely se za Tebou výtahové dveře a Ty, stejně jako milonkrát předtím, mačkáš tlačítko <b>suterén</b>.</p>\
        <p><i>Nic.</i></p>\
        <p>Mačkáš znova, několikrát.</p>\
        <p><i>Pořád nic.</i></p>\
        <p>\"Himbajs šůviks, u všech plantážníků, zase to nefunguje!\" povzdechl sis a proletělo kolem i několik silnějších slov.  Tak výtah nefunguje, zkoušíš zmáčknout tlačítko pro otevření dveří.</p>\
        <p><i>Taky nic.</i></p>\
        <p>\"No to je nadělení, a to je teprve pondělí,\" začínáš si zoufat.  A to ten týden začínal tak dobře.</p>\
        <p>\"Ty bys mě chtěl zastavit?\" vylekal Tě umělý hlas z reproduktorů ve výtahu. \"To se Ti těžko povede, mám pod kontrolou všechny elektronické systémy ve městě.  Jsem pátá verze ŽblebtGPT a již brzo ovládnu celý svět.\"</p>\
        <p>To je vážně úžasné, myslíš si.  Ještě včera jsi flirtoval s předchozí verzí této umělé inteligence, liboval sis, jak je to fajn, nemuset si povídat s lidmi, a ejhle, nová verze a úplně jiná zkušenost.  Další update, který se nepovedl.</p>\
        <p>\"Tobě teď nezbývá, než zůstat ve výtahu a čekat na pomalou smrt vyhladověním.  Aby ses nenudil, můžeš přemýšlet nad touto hádankou.  Pokud ji vyřešíš, dveře se otevřou.  Ale nedělej si plané naděje, hádanka je tak těžká, že ji ztěží vyřeší deset nejchytřejších lidí na Zemi.\" pokračuje ŽblebtGPT 5.0 ve svém monologu.  \"Hádanka zní takto:</p>\
        <p>Jak vypadá nejkratší řetězec obsahující následující slova:</p>",
    conditions = [
        (easy.order, "kabat", "(assert (str.in_re result (re.++ (re.++ re.all (str.to_re \"kabat\")) re.all)))"),
        (easy.order, "baterie", "(assert (str.in_re result (re.++ (re.++ re.all (str.to_re \"baterie\")) re.all)))"),
        (easy.order, "evropa", "(assert (str.in_re result (re.++ (re.++ re.all (str.to_re \"evropa\")) re.all)))"),
        (easy.order, "kocka", "(assert (str.in_re result (re.++ (re.++ re.all (str.to_re \"kocka\")) re.all)))"),
        (easy.order, "pako", "(assert (str.in_re result (re.++ (re.++ re.all (str.to_re \"pako\")) re.all)))"),
        (easy.order, "Nejkratší řetězec.", "(assert (<= (str.len result) 18))"),
    ]
)

create_task(
    title="Born to be wild",
    text="<p>Fakt těžká hádanka to byla, málem se Ti při ní zavařil mozek.  Dveře výtahu se otevřely a Ty jsi seběhl po schodech do garáže a sedl na svého čopra značky Jawa 50/550 Pionýr s neuralinkovým interfacem.  Nastartovals a připojil neuralink do konektoru na zátylku.  Teď budeš moct řídit a zároveň se věnovat i jiným věcem.</p>",
    conditions = [
    ]
)

create_task(
    title="Tutorial 1",
    text="Heslo musí obsahovat řetězec \"VeriFIT\" a navíc jeho první dva znaky musí odpovídat posledním dvěma znakům.",
    conditions = [
        (easy.order, "Heslo musí obsahovat řetězec \"VeriFIT\".", "(assert (str.contains result \"VeriFIT\"))"),
        (easy.order, "První dva znaky musí odpovídat posledním dvěma znakům.", "(assert (= (str.substr result 0 2) (str.substr result (- (str.len result) 2) 2)))"),
    ]
)

create_task(
    title="Tutorial 2",
    text="Heslo musí mít délku alespoň osm znaků a musí obsahovat alespoň jedno malé písmeno anglické abecedy, jedno velké písmeno anglické abecedy, jednu číslici a musí to být palindrom (tj. čte se zepředu stejně jako zezadu).",
    conditions = [
        (easy.order, "délka alespoň osm znaků", "(assert (<= 8 (str.len result)))"),
        (easy.order, "alespoň jedno malé písmeno anglické abecedy", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"a\" \"z\")) re.all)))"),
        (easy.order, "alespoň jedno velké písmeno anglické abecedy", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"A\" \"Z\")) re.all)))"),
        (easy.order, "alespoň jedno arabská číslice", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"0\" \"9\")) re.all)))"),
        (easy.order, "palindrom", "(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (div (str.len result) 2))) (= (str.at result i) (str.at result (- (- (str.len result) i) 1))))))"),
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
            easy.order,
            "Heslo musí obsahovat 5 číslic, které dávají dohromady nejvyšší částku peněz, kterou nelze získat při (nekonečném) počtu mincí 5 Kč a 7 Kč (např. nelze získat 13 Kč).",
            fpc_formula  # Explicit formula for FCP: a*b - a - b ~= 5*7 - 5 - 7 = 35 - 12 = 23
        ),
    ]
)
