Úvod do regexů
==============

* `a` - zachytí text, ve kterém se kdekoliv vyskytuje symbol `a`, propustí ostatní texty (podobně pro ostatní symboly)
  * příklady zachycení: `Gargamel`, `Jirka`, `Šmoulinka`, `Kobyla má malý bok`
  * příklady propuštení: `hobit`, `Andrej` (`A` a `a` jsou různé symboly!), `jáhly` (`á` a `a` jsou různé symboly)

* `abc` - zachytí text, ve kterém se kdekoliv vyskytuje řetězec `abc`
  * příklady zachycení: `mám rád časopis abc`, `abcdefghijklmnopqrstuvwzyx`
  * příklady propuštení: `babička`

* `.` - zachytí libovolný znak
	* příklady zachycení pro regex `n.z.ar`: `nazdar`, `nezmar`

* `(ab)*` - zachytí text obsahující nula či více výskytů řetězce `ab` za sebou (pro jeden znak nejsou potřeba závorky)
  * příklady zachycení pro regex `0(xy)*1`: `10xy10`, `ABC0xyxyxy1DEF`, `1010` (nula výskytů), `1001` (nula výskytů)
  * příklady propuštění pro regex `0(xy)*1`: `11110000`, `0yx1`


* `^ahoj` - zachytí text, ve kterém je řetězec `ahoj` na začátku řádku

* `konec$` - zachytí text, ve kterém je řetězec `konec` na konci řádku

* `(jedna)|(dva)` - zachytí text, ve kterém se vyskytuje řetězec `jedna` nebo řetězec `dva` (pozor na nutnost použití závorek pro řetězce delší než jeden znak!)

* `\x` - ruší speciální význam symbolu `x`:
  * příklad zachycení pro regex`\(pozn\.`: `v létě bývá teplo (pozn. v zimě zase zima)` (ruší se speciální význam symbolu `(`)
  * příklad propuštení pro regex `\(pozn\.`: `na jaře se probouzí plazi (poznamenala ještěrka)` (ruší se speciální význam symbolů `(` a `.`)