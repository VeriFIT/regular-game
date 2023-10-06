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
        <p>No tak ani s pamětí na mnemotechnické pomůcky to nebylo žádná sláva.  Asi Ti nezbývá, než sednout na čopra a jet na velitelsví osobně.  Ukousnul sis poslední sousto z toustu, dopil kávu (AI apokalypsa počká), hodil na sebe bundu a vyběhl z bytu, rovnou do výtahu.  Zavřely se za Tebou výtahové dveře a Ty, stejně jako milionkrát předtím, mačkáš tlačítko <b>suterén</b>.</p>\
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
<p>Vyjel jsi z garáže, projel podivně zmlklým městem a najel na dálnici.  Dosud jsi nepotkal ani živáčka.  Na dálnici prázdno.  Nakopnul jsi tachyonový stabilizátor a rozjel se závratnou rychlostí. Směr: Velitelství FDTO.  Aspoň, že dálnice je prázdná a nemusíš kličkovat mezi auty a předjíždějícími se kamiony.</p>
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
<p>S fungující převodovkou se Ti podařilo vyjet s houfnicí na dálnici a pokračovat v cestě na velitelství FDTO.</p>
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
          "1e0f6590",
          "5f49e199",
          "2f6e44d8",
          "93864229",
          "0d286d10",
          "d5ca4882",
          "49333d1b",
          "66798b9c",
          "f3f2b273",
          "640869d7",
          "00643b50",
          "dde6f5f7",
          "2a645814",
          "2be5d75e",
          "4f2e91a1",
          "e50e6920",
          "81b28741",
          "611f9b6d",
          "9117581b",
          "a0940d74",
          "9aef268e",
          "b3c4b32c",
          "b4b4ba85",
          "bbdfb93e",
          "66f64424",
          "8b954089",
          "d6e59784",
          "254e9e62",
          "e313a351",
          "b4c551f4",
          "4ae0010e",
          "cf2b9b29",
          "a4020770",
          "61f8dae9",
          "532fb90b",
          "c6d43bbe",
          "ea8282bf",
          "3f294547",
          "cdfc62ef",
          "6ea7a88f",
          "160a0202",
          "896df3d3",
          "6da4dd8c",
          "24b36fc1",
          "9dc4fc90",
          "1f4f6d3e",
          "5668003c",
          "53b4f942",
          "c2008f7e",
          "63f33917",
          "ec284886",
          "01475a61",
          "aa2af805",
          "6e83a47a",
          "d2ab5e98",
          "feb390ba",
          "afcada61",
          "57ee483a",
          "a607af9d",
          "68ac68c7",
          "5a443c09",
          "31f97173",
          "5ca03075",
          "ea932062",
          "0308864b",
          "8a86eb23",
          "f06b6931",
          "d65bcccc",
          "bbfd3004",
          "dd722d6d",
          "6a66e552",
          "893bd109",
          "e9493a1f",
          "7989d4f0",
          "bd8ab053",
          "aa2fc237",
          "b5d70565",
          "e791b9d0",
          "dc51d095",
          "41848811",
          "6ab45550",
          "9ed05250",
          "9a9adfd9",
          "fff62b87",
          "015c9dc6",
          "7f1ae6ac",
          "27c10c47",
          "7f8c67ef",
          "00df752b",
          "ba32ab88",
          "cdfc7249",
          "ff21206e",
          "63d7c133",
          "74766d44",
          "96a25e82",
          "a04df236",
          "1ae65f8a",
          "bb13146e",
          "5bf63dd0",
          "4da32288",
        ]

keys2 = [
        "f6e2ebf7",
        "6f1e351d",
        "d82be7d1",
        "ef930287",
        "7d138fd8",
        "fd87fcb5",
        "8c5a4e32",
        "024dd41c",
        "5ba82d8b",
        "c191e5d3",
        "15bd3e00",
        "7434e687",
        "1274d2ea",
        "3536bcf3",
        "51f85269",
        "caf247f3",
        "e07f9f26",
        "0e25fc56",
        "ede740aa",
        "d31584f4",
        "8cd45031",
        "98512c78",
        "16e8c695",
        "75c6cab2",
        "48cde2ac",
        "1bf4a67b",
        "be4f3858",
        "7159b5fc",
        "3f5b495e",
        "a4242b14",
        "f560e3c8",
        "7b5051ed",
        "9bf6adc0",
        "5405c16f",
        "058bb929",
        "32df9b84",
        "5ca6a76b",
        "4436e3fb",
        "a2f9287b",
        "2533ed16",
        "2eb19d64",
        "2cc1bcd2",
        "e1b35987",
        "c8ef218a",
        "287eda14",
        "32052e9f",
        "3d458390",
        "75258e23",
        "477ad385",
        "b86c197f",
        "53ac2b46",
        "26c396f7",
        "07f0943c",
        "b7d42c22",
        "dd3b4eb6",
        "3d936939",
        "dc27ca5e",
        "56177916",
        "c53bf49b",
        "3ef7c26d",
        "d0f27f6c",
        "3df04276",
        "10a8082d",
        "8ef51e8c",
        "8c8fd878",
        "ec51049a",
        "85970791",
        "791dc3de",
        "6f26ec89",
        "749fa5e8",
        "d7813202",
        "45d1d0a2",
        "453d420e",
        "4b84e433",
        "0a28678b",
        "4571b16b",
        "39606c14",
        "025b2ccd",
        "06136e6b",
        "6f3c1122",
        "72c2f42d",
        "7d66daee",
        "a3d85103",
        "f09b1fba",
        "c0a75921",
        "1bb79a1c",
        "7ca2db34",
        "6e1cea8a",
        "3d7f3fe0",
        "8613529d",
        "236611b6",
        "ea0051cd",
        "5266ba49",
        "2f2f9e7d",
        "1207dfc6",
        "ebc2cfd1",
        "75ad6f2a",
        "15cabca6",
        "d45bd20e",
        "91850eaa",
        ]

keys3 = [
        "81f556c0",
        "02f6e58d",
        "8005c9d5",
        "cf1c9bfd",
        "e4bb4f03",
        "d00edc8c",
        "f71a2566",
        "54b1286d",
        "a02c1347",
        "0be3842b",
        "66a6d29a",
        "5f554a9f",
        "ac06ed46",
        "ad3734aa",
        "c7894e41",
        "577c5f15",
        "33b26075",
        "d22d102f",
        "cc05820b",
        "0fa54c66",
        "a1a9bfcc",
        "11365cac",
        "270f97c2",
        "feacdc4e",
        "343158b0",
        "ac278aaa",
        "8f17718b",
        "500ce6af",
        "a7bd8c8d",
        "004055e9",
        "a51aebe3",
        "fcef63e3",
        "8a143096",
        "6b1155c9",
        "23319b77",
        "ab62e1d4",
        "a3b5a943",
        "94594931",
        "bc386507",
        "352a1be8",
        "037c6e7c",
        "54721230",
        "4d4f8d52",
        "c1238838",
        "42cf8e63",
        "f7cf8bcd",
        "38dc41f8",
        "cf2df1ef",
        "1ccc1b94",
        "8ec7cc8d",
        "a28646e6",
        "962394ab",
        "7366873e",
        "1aa4856d",
        "2c67f557",
        "8c676ca4",
        "9a1419af",
        "8664870c",
        "50c1527a",
        "6794ea2a",
        "32d2c0f5",
        "3faff0e3",
        "1bce3bdb",
        "580a3b82",
        "d7868ef4",
        "ec88bbf0",
        "efd7b4fd",
        "4118bc01",
        "f8055361",
        "54b9f0ab",
        "8dcfff11",
        "333955aa",
        "b5feac4e",
        "3c744dde",
        "69764eab",
        "49b1de1c",
        "99ae25ce",
        "72ade5a1",
        "d7bc2536",
        "bedd9888",
        "531a9604",
        "4742b1de",
        "83649d7e",
        "4fa22bdc",
        "821237f6",
        "6ee0f663",
        "2c0d8389",
        "7e95f73c",
        "4f0733be",
        "3e55da32",
        "3e01ef0b",
        "638b0194",
        "559ddc9d",
        "6f25a2c0",
        "00f7f551",
        "07c35365",
        "ac6ee1ea",
        "a30f7e28",
        "e31a1306",
        "6a027d3f",
        "223be608",
        ]

keys4 = [
        "90c7cd01",
        "3614df96",
        "af275cc8",
        "77e09624",
        "22657298",
        "38539bfc",
        "f0983c8d",
        "b89bb629",
        "0df0bb8d",
        "d1aa694c",
        "a0efbf36",
        "53479816",
        "98710bfd",
        "d0c94d70",
        "b90b910e",
        "9440cc7d",
        "67f290c2",
        "6e0a06ec",
        "b893272b",
        "8428fca5",
        "3e0ea2a8",
        "f44b3ade",
        "09a630af",
        "b642a843",
        "6d8e3078",
        "00b58698",
        "aefe4a52",
        "dad490f0",
        "ba5f3201",
        "a53ec6b8",
        "7ea1e694",
        "f4d8dccf",
        "b68b8fea",
        "16c7a895",
        "5f8509c1",
        "1109fbf8",
        "1a9f0512",
        "c44f741d",
        "183feda7",
        "5476704c",
        "cdd2de05",
        "d39ce3e6",
        "afdfafc6",
        "cd1d18ad",
        "f1f0fe55",
        "fb893fb5",
        "851f6b50",
        "1366d468",
        "cb754102",
        "48934532",
        "7d87663d",
        "b65ad023",
        "0c69e8b2",
        "e4f23362",
        "0c5988ff",
        "02f3b9ab",
        "e23418d8",
        "4d2535c2",
        "52922c0c",
        "d0c1ddfc",
        "2f266752",
        "c4dc538e",
        "c6417387",
        "8bf0f3f0",
        "78899d71",
        "51a135b0",
        "06861025",
        "5e985994",
        "261c0a61",
        "333393d9",
        "f98f074b",
        "e47ea079",
        "564abae4",
        "4cbe3740",
        "e3b8f7e2",
        "7830814f",
        "386ddd60",
        "bd65bec2",
        "0f1d8f38",
        "dcf60037",
        "3f8706b4",
        "e9b37a8b",
        "5020398f",
        "d6665fc4",
        "c5fb8549",
        "db59adab",
        "2354b171",
        "a60e700d",
        "cb4497a1",
        "425bc5c6",
        "0979f01c",
        "671308f6",
        "b9f425e5",
        "a51e1c7e",
        "37d50b0c",
        "f045a81f",
        "9782e73b",
        "08e17c95",
        "30193917",
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


