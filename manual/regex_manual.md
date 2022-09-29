Úvod do regexů
==============

* `a` - zachytí text, ve kterém se kdekoliv vyskytuje symbol `a`, propustí ostatní texty (podobně pro ostatní symboly)
  * příklady zachycení: `Gargamel`, `Jirka`, `Šmoulinka`, `Kobyla má malý bok`
  * příklady propuštění: `hobit`, `Andrej` (`A` a `a` jsou různé symboly!), `jáhly` (`á` a `a` jsou různé symboly)
* `abc` - zachytí text, ve kterém se kdekoliv vyskytuje řetězec `abc`
  * příklady zachycení: `mám rád časopis abc`, `abcdefghijklmnopqrstuvwzyx`
  * příklady propuštění: `babička`
* `.` - zachytí libovolný znak
	* příklady zachycení pro regex `n.z.ar`: `nazdar`, `nezmar`
* `[abc]` - zachytí libovolný ze znaků `a`, `b`, `c` (lze použít i rozsah, např. `[a-z]` pro *všechna malá* písmena anglické abecedy nebo `[a-zA-Z]` pro *všechna* písmena anglické abecedy)
* `(ab)*` - zachytí text obsahující nula či více výskytů řetězce `ab` za sebou (pro jeden znak nejsou potřeba závorky)
  * příklady zachycení pro regex `0(xy)*1`: `10xy10`, `ABC0xyxyxy1DEF`, `1010` (nula výskytů), `1001` (nula výskytů)
  * příklady propuštění pro regex `0(xy)*1`: `11110000`, `0yx1`
* `(ab)+` - jako `(ab)*`, ale pro *alespoň jeden* výskyt
* `(ab)?` - nula nebo jeden výskyt řetězce `ab`
* `(ab){4}` - 4 opakování řetězce `ab`, např. `123abababab67`
* `(ab){2,4}` - 2&ndash;4 opakování řetězce `ab`, např. `123ababab67`
* `^ahoj` - zachytí text, ve kterém je řetězec `ahoj` na začátku řádku
* `konec$` - zachytí text, ve kterém je řetězec `konec` na konci řádku
* `jedna|dva` - zachytí text, ve kterém se vyskytuje řetězec `jedna` nebo řetězec `dva`
* `\x` - ruší speciální význam symbolu `x`:
  * příklad zachycení pro regex `\(pozn\.`: `v létě bývá teplo (pozn. v zimě zase zima)` (ruší se speciální význam symbolu `(`)
  * příklad propuštění pro regex `\(pozn\.`: `na jaře se probouzí plazi (poznamenala ještěrka)` (ruší se speciální význam symbolů `(` a `.`)
