Úvod do regexů
==============

* `a` - zachytí text, ve kterém se kdekoliv vyskytuje symbol `a`, propustí ostatní texty (podobně pro ostatní symboly)
  * příklady zachycení: `Gargamel`, `Jirka`, `Šmoulinka`, `Kobyla má malý bok`
  * příklady propuštení: `hobit`, `Andrej` (`A` a `a` jsou různé symboly!), `jáhly` (`á` a `a` jsou různé symboly)

* `abc` - zachytí text, ve kterém se kdekoliv vyskytuje řetězec `abc`
  * příklady zachycení: `mám rád časopis abc`, `abcdefghijklmnopqrstuvwzyx`
  * příklady propuštení: `babička`

* `^ahoj` - zachytí text, ve kterém je řetězec `ahoj` na začátku řádku

* `konec$` - zachytí text, ve kterém je řetězec `konec` na konci řádku

* `(jedna)|(dva)` - zachytí text, ve kterém se vyskytuje řetězec `jedna` nebo řetězec `dva` (pozor na nutnost použití závorek!)

* `\x` - ruší speciální význam symbolu `x`:
  * příklady zachycení pro `\(pozn\.`: `v létě bývá teplo (pozn. v zimě zase zima)` (ruší se speciální význam symbolu `(`)
  * příklady propuštení pro `\(pozn\.`: `na jaře se probouzí plazi (poznamenala ještěrka)` (ruší se speciální význam symbolů `(` a `.`)