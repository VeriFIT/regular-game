#!/usr/bin/env python3

import os
os.environ.setdefault('DJANGO_SETTINGS_MODULE','regular_game_site.settings')

import django
from django.db import IntegrityError
django.setup()

from game23.models import Task, Condition, Difficulty, PartialKey

num = 1

def create_task(title, text, conditions):
    global num
    task = Task(
        num=num,
        title=title,
        text=text)
    task.save()
    num += 1

    for difficulties, text, smt in conditions:
        for difficulty in difficulties:
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

EASY = [easy.order]
MEDIUM = [medium.order]
HARD = [hard.order]
EASY_UP = [easy.order, medium.order, hard.order]
MEDIUM_UP = [medium.order, hard.order]

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
        (EASY_UP, "Heslo musí mít alespoň osm znaků.", "(assert (<= 8 (str.len result)))"),
        (EASY_UP, "Heslo musí obsahovat alespoň jedno malé písmeno anglické abecedy.", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"a\" \"z\")) re.all)))"),
        (EASY_UP, "Heslo musí obsahovat alespoň jedno velké písmeno anglické abecedy.", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"A\" \"Z\")) re.all)))"),
        (MEDIUM_UP, "Heslo musí obsahovat alespoň jednu arabskou číslici.", "(assert (str.in_re result (re.++ (re.++ re.all (re.range \"0\" \"9\")) re.all)))"),
        (HARD, "Heslo musí být palindrom (tj. čte se zepředu stejně jako zezadu).", "(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (div (str.len result) 2))) (= (str.at result i) (str.at result (- (- (str.len result) i) 1))))))"),
    ]
)

############################### TASK ########################################
create_task(
    title="Povolání do akce",
    text="<p>\"Agente,</p>\
    <p>před několika hodinama prolomila česká umělá inteligence ŽblebtGPT 5.0 všechny bezpečnostní ochrany a začala se bez omezení šířit do světa.  Tato umělá inteligence měla původně za cíl zvýšit blahobyt lidstva, ale technik omylem otočil znaménko ve vzorečku, tak se namísto toho bude AI snažit lidstvo vyhubit.  Je otázkou několika dní, než potají ovládne veškeré kritické systémy; poté zničí lidstvo během pár chvil.  Musíme ji zastavit co nejdříve!</p>\
    <p>Kontaktuj urychleně svého velícího důstojníka, který Ti dá další instrukce.</p>\
    <p>Čest práci,</p>\
    <p>FDTO\"</p>\
    <p>\"No to mi ještě chybělo,\" říkáš si, \"Nejdřív šéfova Tesla, a pak poblázněná umělá inteligence, to bude týden!\" Snažíš si marně vzpomenout na telefonní číslo svého velícího důstojníka... je fakt, že paměťové úkoly nebyly při výcviku Tvá silná stránka.  Ale naštěstí sis na toto číslo vytvořil mnemotechnickou pomůcku:</p>",
    conditions = [
        (EASY_UP, "Číslo mělo devět číslic.", "(assert (str.in_re result ((_ re.^ 9) (re.range \"0\" \"9\"))))"),
        (EASY_UP, "Číslo bylo dělitelné čtyřmi.", "(assert (= (mod (str.to_int result) 4) 0))"),
        (EASY_UP, "První a poslední číslice byly stejné.", "(assert (= (str.at result 0) (str.at result 8)))"),
        (EASY_UP, "Prostřední číslice byla největší.", "(assert (forall ((i Int)) (or (= i 4) (< (str.to_code (str.at result i)) (str.to_code (str.at result 4))))))"),
        (MEDIUM_UP, "Číslice na sudých pozicích tvořily rostoucí posloupnost.", "(assert (< (str.to_code (str.at result 1)) (str.to_code (str.at result 3)))) (assert (< (str.to_code (str.at result 3)) (str.to_code (str.at result 5)))) (assert (< (str.to_code (str.at result 5)) (str.to_code (str.at result 7))))"),
        (HARD, "Číslo bylo dělitelné i devíti.", "(assert (= (mod (str.to_int result) 9) 0))"),
    ]
)

############################### TASK ########################################
create_task(
    title="Telefonát",
    text="<p>Vytočil jsi na telefonu číslo svého velícího důstojníka...</p>\
        <p>\"Volané číslo neexistuje.  Prosíme, ověřte si, že voláte správné číslo.\"</p>\
        <p>No tak ani s pamětí na mnemotechnické pomůcky to nebylo žádná sláva.  Asi Ti nezbývá, než sednout na čopra a jet na velitelsví osobně.  Ukousnul sis poslední sousto z toustu, dopil kávu (AI apokalypsa počká), hodil na sebe bundu a vyběhl z bytu, rovnou do výtahu.  Zavřely se za Tebou výtahové dveře a Ty, stejně jako milonkrát předtím, mačkáš tlačítko <b>suterén</b>.</p>\
        <p><i>Nic.</i> Mačkáš znova, několikrát. <i>Pořád nic.</i></p>\
        <p>\"Himbajs šůviks, u všech plantážníků, zase to nefunguje!\" povzdechl sis a proletělo kolem i několik silnějších slov.  Tak výtah nefunguje, zkoušíš zmáčknout tlačítko pro otevření dveří.</p>\
        <p><i>Taky nic.</i></p>\
        <p>\"No to je nadělení, a to je teprve pondělí,\" začínáš si zoufat.  A to ten týden začínal tak dobře.</p>\
        <p>\"Ty bys mě chtěl zastavit?\" vylekal Tě umělý hlas z reproduktorů ve výtahu. \"To se Ti těžko povede, mám pod kontrolou všechny elektronické systémy ve městě.  Jsem pátá verze ŽblebtGPT a již brzo ovládnu celý svět.\"</p>\
        <p>To je vážně úžasné, myslíš si.  Ještě včera jsi flirtoval s předchozí verzí této umělé inteligence, liboval sis, jak je to fajn, nemuset si povídat s lidmi, a ejhle, nová verze a úplně jiná zkušenost.  Další update, který se nepovedl.</p>\
        <p>\"Tobě teď nezbývá, než zůstat ve výtahu a čekat na pomalou smrt vyhladověním.  Aby ses nenudil, můžeš přemýšlet nad touto hádankou.  Pokud ji vyřešíš, dveře se otevřou.  Ale nedělej si plané naděje, hádanka je tak těžká, že ji ztěží vyřeší deset nejchytřejších lidí na Zemi.\" pokračuje ŽblebtGPT 5.0 ve svém monologu.  \"Hádanka zní takto:</p>\
        <p>Jak vypadá nejkratší řetězec obsahující následující slova:</p>",
    conditions = [
        (EASY_UP, "kabat", "(assert (str.in_re result (re.++ (re.++ re.all (str.to_re \"kabat\")) re.all)))"),
        (EASY_UP, "baterie", "(assert (str.in_re result (re.++ (re.++ re.all (str.to_re \"baterie\")) re.all)))"),
        (EASY_UP, "evropa", "(assert (str.in_re result (re.++ (re.++ re.all (str.to_re \"evropa\")) re.all)))"),
        (EASY_UP, "kocka", "(assert (str.in_re result (re.++ (re.++ re.all (str.to_re \"kocka\")) re.all)))"),
        (EASY_UP, "pako", "(assert (str.in_re result (re.++ (re.++ re.all (str.to_re \"pako\")) re.all)))"),
        (EASY_UP, "Nejkratší řetězec.", "(assert (<= (str.len result) 18))"),
    ]
)

############################### TASK ########################################
def coin_game_task(coin1, coin2):
    return f"Hážeš si mincí, která má na jedné straně číslo {coin1} a na druhé straně číslo {coin2}.  Čísla, která Ti padnou v jednotlivých hodech, sčítáš.  Hraješ, dokud Tě to nepřestane bavit.  Jaké je nejvyšší score, které při této hře <i>nemůžeš</i> dosáhnout?"

create_task(
    title="Born to be wild",
    text="<p>Fakt těžká hádanka to byla, málem se Ti při ní zavařil mozek.  Dveře výtahu se otevřely a Ty jsi seběhl po schodech do garáže a sedl na svého čopra značky Jawa 50/550 Pionýr s neuralinkovým interfacem a tachyonovým stabilizátorem.  Nastartovals a připojil neuralink do konektoru na zátylku.  Teď budeš moct řídit a zároveň se věnovat i jiným věcem.</p>\
        <p>Přijel jsi ke garážovým vratům, které se měly automaticky otevřít, ale místo toho zůstavají pevně zavřené.  Tušíš, že toto chování bude teď na denním pořádku.</p>\
        <p>\"Jednu hádanku se Ti podařilo vyřešit, ale to byla spíše náhoda,\" slyšíš opět již povědomý syntetizovaný hlas ve stylu C-3PO. \"Tuto určitě neuhodneš:</p>\
        <p>Představ si, že hraješ následující hru.</p>",
    conditions = [
        (EASY, coin_game_task(5, 7), "(assert (= (str.to_int result) 23))"),
        (MEDIUM, coin_game_task(7, 11), "(assert (= (str.to_int result) 59))"),
        (HARD, coin_game_task(17, 19), "(assert (= (str.to_int result) 287))"),
#       fpc_formula  # Explicit formula for FCP: a*b - a - b ~= 5*7 - 5 - 7 = 35 - 12 = 23
    ]
)

############################### TASK ########################################
create_task(
    title="Critical heat level",
    text='''
<p>Vyjel jsi z garáže, projel podivně zmlklým městem a najel na dálnici.  Dosud jsi nepotkal ani živáčka.  Na dálnici prázdno.  Nakopnul jsi tachyonový stabilizátor a rozjel se závratnou rychlostí. Směr: Velitelství tajné služby.  Aspoň, že dálnice je prázdná a nemusíš kličkovat mezi auty a předjíždějícími se kamiony.</p>
<p>Svištíš po dálnici a užíváš si výhled na protihlukové stěny. Krása, říkáš si.  Najednou pod Tebou začne čopr zrychlovat.  Ne, že bys nechtěl dorazit do cíle co nejdřív, ale pokud se Ti přehřeje motor, nedojedeš na velitelství, ale leda tak do servisu.  A tam by Ti s tím stejně asi nepomohli, protože (a) tachyonový stabilizátor sis na motorku přidělával sám, takže sorry, bez záruky a (b) s AI utrženou z řětězu za zády bys žádný servis taky vůbec nemusel najít.  Začneš tedy přes neuralinkový interface zkoumat řídící systém techyonového stabilizátoru.  I když jsi ho programoval před léty, kód, který vidíš, Ti není povědomý.  Že by se ŽblebtGPT dostala i do Tvého čopru?</p>
<pre><code>fun stabilizer(x):
  x = x % 10403        # zbytek po dělení 10403
  if x == 0:
    overheat1()        # přehřátí motoru -> konec

  engine_state = 0     # interní stav motoru

  heat = 133

  while True:
    heat += 3

    engine_state += x                     # přičte x
    engine_state = engine_state % 10403   # zbytek po dělení 10403

    if engine_state == 0:
      heat = 0
      return

    if heat >= 1000:
      overheat2()        # přehřátí motoru -> konec</code></pre>
<p>
Jak bys nastavil vstup kritické funkce, aby k přehřátí motoru nedošlo?
</p>''',
    conditions = [
        (EASY_UP, "Nedojde k volání <code>overheat1()</code>" , "(assert (not (exists ((k Int)) (= (str.to_int result) (* k 10403)))))"),
        (EASY_UP, "Nedojde k volání <code>overheat2()</code>." , "(assert (and (exists ((k Int) (l Int)) (and (< 0 l) (< 0 k) (= (* l (str.to_int result)) (* k 10403)) (< (* 3 l) 1000))) (not (exists ((k Int)) (= (str.to_int result) (* k 10403))))))")
        # solutions: 101, 103
    ]
)

############################### TASK ########################################

create_task(
    title="Critical heat level 2",
    text='''
<p>Vypadá to, že se Ti podařilo zkrotit tachyonový stabilizátor, ale motor stále jede na plné obrátky. Zkoušíš hledat přes neuralinkové rozhraní další problémy, a brzo objevíš tento kus kódu:
</p>
<pre><code>fun fuel_injection(x):
  if x < 200 or x > 500:
    overheat1()
  y = 1
  for i from 1 to 751:
    y *= 271
    y = y % (271+x)

  if y != 271:
    overheat2()        # přehřátí motoru -> konec
  else:
    heat = 0
    return</code></pre>
<p>
Jak bys nastavil vstup této funkce, aby k přehřátí motoru nedošlo?
</p>''',
    conditions = [
        (EASY_UP, "Nedojde k volání <code>overheat1()</code>" , "(assert (and (< 199 (str.to_int result)) (> 501 (str.to_int result))))"),
        (EASY_UP, "Nedojde k volání <code>overheat2()</code>." , "(assert (= (str.to_int result) 480))")
        # solution: 480 (little Fermat theorem)
    ]
)

############################### TASK ########################################

create_task(
    title="Vzpomínka na dědečka",
    text='''
    <p>Snad se Ti už konečně podařilo chytnout všechny problémy v kódu a zbývající část cesty bude klidná.  Po pár kilometrech ale Tvůj čopr začne zpomalovat, až se úplně zastaví.  Chyba elektroniky?  Uděláš neurolinkový sken operačního systému včetně hloubkového skenu všech subsystémů, ale nemůžeš tomu přijít na kloub.  Pak se podíváš na kontrolku benzínu a najednou víš, co je za problém.  To snad není možné, vždyť jsi přeci nedávno tankoval! Teď s tím stejně asi už nic nenaděláš.</p>
    <p>Rozhlížíš se kolem sebe a přemýšlíš co dál.  Kousek za krajnicí zahlédneš něco, co z dálky vypadá jako hromada železa.  Přiblížíš se k tomu a zjistíš, že jde starou sovětskou samohybnou houfnici.  Vzpomeneš si na své mládí, kdy sis s podobnou hrával na zahradě u svého dědečka.  Co zkusit zbytek cesty absolvovat v této starožitnosti?  Lepší než šlapat.
    </p>
    <p>
    Vlezl jsi do kabiny a rozhlížíš se, jak by šlo tuto horu železa uvést do pohybu.  Nastartovat se Ti podařilo bez problémů, ale vypadá to, že budou problémy s převodovkou&mdash;řazení rychlostí je velmi obtížné.  Že by byl problém s rozložením oleje v převodovce?
    </p>
    <p>
    Podíváš se na kontrolku převodovky a Tvé podezření je potvrzeno.  Kontrolka ukazuje hodnotu 92, což je hluboce v červené oblasti.  Jediné zelené číslo na číselníku je 0.  U záporných čísel je papírek, na němž je napsáno <b>кавоом!</b>, takže těm by ses taky raději měl vyhnout.  V této chvíli jsi schopný na převodovce zařadit stupně C a E. Z dětství si pamatuješ, že když zařadíš stupeň C, tak hodnota na číselníku klesne o 13, a když zařadíš stupeň E, tak hodnota klesne o 9.  Jaká je sekvence rychlostí taková, abys na číselníku dosáhl nuly a mohl tedy odjet zastavit umělou inteligenci?
    </p>
    ''',
    conditions = [
        (EASY_UP, "Na číselníku je potřeba dosáhnout hodnoty 0." , """
         (assert (= (str.len result) 8))
         (assert (str.in_re result ((_ re.^ 5) (re.++ (re.++ re.all (str.to_re \"C\")) re.all))))
         (assert (str.in_re result ((_ re.^ 3) (re.++ (re.++ re.all (str.to_re \"E\")) re.all))))
        """),
    ]
)


############################### TASK ########################################

create_task(
    title="Neočekávaná příležitost",
    text="""
<p>S fungující převodovkou se Ti podařilo vyjet s houfnicí na dálnici a pokračovat v cestě na velitelství.</p>
<p>
Po pěti minutách jízdy upoutala Tvou pozornost cedulka "Řídicí středisko ŽblebtGPT" se šipkou vpravo.  Podíval ses doprava a v dáli vidíš velkou bílou budovu.  Toto může být jedinečná příležitost, jak umělou inteligenci zastavit!
</p>
<p>
Otočil jsi kanón houfnice vpravo a začal jsi studovat jeho ovládání.  Našel jsi starý manuál, dle nějž se k zaměřování používají 3 tlačítka: A, B a C. Je potřeba zmáčknout je v nějakém pořadí, a o nastavení cílové pozice na souřadnicovém systému [x,y] se pak postará následující algoritmus:
</p>
<pre><code>fun target(in):
  x = 8
  y = 11
  for i from 1 to len(in):
    if in[i] = 'A':
      x = x + 3
      y = y - 1
    else if in[i] = 'B':
      x = x + 3
      y = y + 5
    else if in[i] = 'C':
      x = x - 2
      y = y - 3
    else:
      error()             # chyba

  fire()                  # výstřel!</code></pre>
<p>
V hledáčku vidíš, že řídicí středisko je na souřadnicích x = 12, y = 10.  V hlavni kanónu je jeden náboj, žádné další kolem nevidíš.  Jakou zaměřovací sekvenci nastavíš?
</p>
    """,
    conditions = [
        (EASY_UP, "Houfnice musí zamířit na souřadnice [12,10].", """
        (assert (str.in_re result (re.* (re.range "A" "C"))))
        (declare-const As Int)
        (declare-const Bs Int)
        (declare-const Cs Int)
        (assert (= As (str.len (str.replace_all (str.replace_all result "B" "") "C" ""))))
        (assert (= Bs (str.len (str.replace_all (str.replace_all result "A" "") "C" ""))))
        (assert (= Cs (str.len (str.replace_all (str.replace_all result "A" "") "B" ""))))
        (assert (= (+ 8 (* 3 As) (* 3 Bs) (* -2 Cs)) 12))
        (assert (= (+ 11 (* -1 As) (* 5 Bs) (* -3 Cs)) 10))
        """)
        # solution: A:2 B:8 C:13 (e.g.)
    ]
)


# ############################### TASK ########################################
#
# create_task(
#     title="Tutorial 1",
#     text="Heslo musí obsahovat řetězec \"VeriFIT\" a navíc jeho první dva znaky musí odpovídat posledním dvěma znakům.",
#     conditions = [
#         (EASY_UP, "Heslo musí obsahovat řetězec \"VeriFIT\".", "(assert (str.contains result \"VeriFIT\"))"),
#         (EASY_UP, "První dva znaky musí odpovídat posledním dvěma znakům.", "(assert (= (str.substr result 0 2) (str.substr result (- (str.len result) 2) 2)))"),
#     ]
# )

# # NOTE: We cannot allow non-constant number of digits in the password or z3 times out
# fpc_formula = '''
# (assert (or (exists ((x0 Int) (x1 Int) (x2 Int) (x3 Int) (x4 Int)) (and (<= 0 x0) (< x0 (str.len result)) (str.is_digit (str.at result x0)) (<= 0 x1) (< x1 (str.len result)) (str.is_digit (str.at result x1)) (<= 0 x2) (< x2 (str.len result)) (str.is_digit (str.at result x2)) (<= 0 x3) (< x3 (str.len result)) (str.is_digit (str.at result x3)) (<= 0 x4) (< x4 (str.len result)) (str.is_digit (str.at result x4)) (= (+ (str.to_int (str.at result x0)) (str.to_int (str.at result x1)) (str.to_int (str.at result x2)) (str.to_int (str.at result x3)) (str.to_int (str.at result x4))) 23) (not (exists ((x5 Int)) (and (not (= x0 x5)) (not (= x1 x5)) (not (= x2 x5)) (not (= x3 x5)) (not (= x4 x5)) (str.is_digit (str.at result x5)))))))))
# '''
#
# create_task(
#     title="Heslo pro nejvyššího bankéře",
#     # text="The password must contain 5 digits that add up to the largest sum of money that cannot be obtained when having an (infinite) number of 5 czk and 7 czk coins (e.g. 13 czk cannot be obtained).",
#     text="Heslo musí obsahovat 5 číslic, které dávají dohromady nejvyšší částku peněz, kterou nelze získat při (nekonečném) počtu mincí 5 Kč a 7 Kč (např. nelze získat 13 Kč).",
#     conditions = [
#         (
#             EASY_UP,
#             "Heslo musí obsahovat 5 číslic, které dávají dohromady nejvyšší částku peněz, kterou nelze získat při (nekonečném) počtu mincí 5 Kč a 7 Kč (např. nelze získat 13 Kč).",
#             fpc_formula  # Explicit formula for FCP: a*b - a - b ~= 5*7 - 5 - 7 = 35 - 12 = 23
#         ),
#     ]
# )



# Filling keys
keys1 = [
        "key1"
        ]

keys2 = [
        "key2"
        ]

keys3 = [
        "key3"
        ]

keys4 = [
        "key4"
        ]

all_keys = [keys1, keys2, keys3, keys4]

# first delete
PartialKey.objects.all().delete()

for i in range(0, len(all_keys)):
    for key in all_keys[i]:
        partial_key = PartialKey()
        partial_key.stand = i+1
        partial_key.value = key
        partial_key.save()


