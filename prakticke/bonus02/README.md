Bonus 2
=======

**Riešenie odovzdávajte podľa
[pokynov na konci tohoto zadania](#technické-detaily-riešenia)
do štvrtka 21.5. 23:59:59.**

Či ste správne vytvorili pull request si môžete overiť
v [tomto zozname PR pre bonus02](https://github.com/pulls?utf8=%E2%9C%93&q=is%3Aopen+is%3Apr+user%3AFMFI-UK-1-AIN-412+base%3Abonus02).

Súbory potrebné pre toto cvičenie si môžete stiahnuť ako jeden zip
[`bonus02.zip`](https://github.com/FMFI-UK-1-AIN-412/lpi/archive/bonus02.zip).

## Logická hádanka (1b)

Nasledujúcu logickú hádanku zakódujte do výrokovej logiky a vyriešte pomocou
SAT solvera. Odovzdávajte program, ktorý vygeneruje vstup pre SAT solver,
pustí SAT solver, načíta a dekóduje výstup a vypíše riešenie.
**V programe (v komentároch) uveďte formuly, ktorými ste problém popísali.**
Na tejto úlohe si môžete všimnúť a precvičiť:
- prácu s nevyslovenými znalosťami o doméne problému
  (<i lang="en">background knowledge</i>, „znalosti na pozadí“), ktoré
  automaticky zahŕňame do našich úvah, ale logickým metódam a nástrojom ich
  musíme ozrejmiť vhodnou teóriou;
- využitie definícií vo výrokovej logike;
- prístup k tvrdeniam *o* pravdivosti tvrdení.

Pán a pani Smithovci a ich dve deti sú typická americká rodina. Vieme, že
**práve dve** tvrdenia z nasledovných sú pravdivé:

- George a Dorothy sú pokrvní príbuzní
- Howard je starší než George
- Virginia je mladšia než Howard
- Virginia je staršia než Dorothy

Aké je krstné meno otca, mamy, syna, dcéry?

Ako prvú vec v tejto úlohe samozrejme musíme vymyslieť, aké výroky budeme
používať. Sú ale dve základné možnosti: *korektnejšia* a *lenivejšia*.

V *korektnejšej* použijeme okrem tvrdení typu „X je otec“, „Y je dcéra“ atď.
aj tvrdenia „X a Y sú pokrvní príbuzní“, „X je starší(-ia) ako Y“ a korektne
vyjadríme vzťahy medzi nimi (kto s kým je / môže byť / nesmie byť
v „typickej americkej rodine“ pokrvný príbuzný, starší, mladší…).

V *lenivejšom* riešení použijeme iba prvý druh tvrdení a vyjadríme naše
tvrdenia už priamo pomocou nich. Tým sme ale kus práce spravili my
(a nenechali ho na SAT solver) a nezapísali sme presne tvrdenia, ktoré sme
mali (a mohli sme sa ľahko pomýliť pri ich prepise). Takéto riešenia tejto
úlohy budeme síce akceptovať, ale dostanú **maximálne 0.5 boda**.

*Pomôcka 1*: Hádanka má práve jedno riešenie. SAT solver môže nájsť viacero
modelov vašej teórie, všetky by však mali rovnako ohodnocovať premenné, ktoré
kódujú riešenie a mali by sa líšiť len ohodnotením pomocných premenných.

*Pomôcka 2*: Okrem explicitne vyslovených podmienok máme aj nejaké nevyslovené
(tzv. *znalosti na pozadí*, angl. *background knowledge*), ktoré sa skrývajú
pod pojmom „typická americká rodina“. Čo všetko pod tým autor hádanky myslel?

*Pomôcka 3*: Ďalšie nevyslovené podmienky, ktoré pri formalizácii musíme
uvažovať, sú typu: Tá istá osoba nemôže byť zároveň otcom aj synom.

*Pomôcka 4*: Zadefinujte obmedzenia na členov rodiny pre pojmy: pokrvní
príbuzní, starší/mladší. Toto úzko súvisí s ujasnením si skutočností v pomôcke 2.
Ktorí členovia rodiny môžu byž pokrvní príbuzní, ktorý člen môže byť starší od
ktorého, …?

*Pomôcka 5*: Keby sme iba jednoducho zakódovali všetky tvrdenia a dali na vstup
SAT solveru, tak by našiel možnosti, kedy sú *všetky* naraz pravdivé. Úloha ale
hovorí, že *práve dve* tvrdenia majú byť pravdivé (a dve teda nepravdivé). Toto
zabezpečíme tak, že použijeme 4 pomocné premenné (jednu pre každé tvrdenie),
ktoré budú pravdivé práve vtedy, keď dotyčné tvrdenie je pravdivé. Čiže na vstup
SAT solveru chceme dať formuly tvaru p1 ↔︎ TVRDENIE1, p2 ↔︎ TVRDENIE2, … (toto
budú samozrejme zakaždým 2 implikácie, ktoré sa môžu skonvertovať na viacero
CNF kláuz) a potom formuly, ktoré zabezpečia, že práve 2 tvrdenia sú pravdivé
a 2 nepravdivé.

*Poznámka*: Tieto ekvivalencie definujú význam pomocných premenných, podobne
ako explicitné definície v logike prvého rádu definujú význam nových
predikátov. Zadefinovaná premenná sa správa ako skratka za príslušné
tvrdenie. Zároveň zastupuje výrok „príslušné tvrdenie je pravdivé“. Preto
môžeme zadefinované premenné použiť na vyjadrenie toho, koľko tvrdení je
pravdivých.

*Pomôcka 6*: Zabezpečiť, že práve 2 tvrdenia sú pravdivé, sa dá napríklad vymenovaním
všetkých možností, čo ale bude DNF, z ktorého roznásobením vznikne veľa klauzúl.
Lepšia možnosť je povedať, že aspoň 2 musia byť pravdivé a nesmie byť viac ako
2 pravdivých (t.j. nesmú byť 3 pravdivé). Jednotlivé možnosti v druhej podmienke
sú negácie konjunkcií, čo sú priamo klauzuly. Prvá podmienka bude ešte stále
DNF, ale iba s konjunkciami s 2 premennými. Dá sa to však tiež vylepšiť, ak ju
preformulujeme ako „nesmú byť viac ako 2 (aspoň 3) nepravdivé“.

## Technické detaily riešenia

Riešenie odovzdajte do vetvy `bonus02` v adresári `prakticke/bonus02/bonus02-{python,java}`.


Odovzdajte súbor [`Rodinka.py`](bonus02-python/Rodinka.py)/[`Rodinka.java`](bonus02-java/Rodinka.java),
v ktorom  implementujete metódu `vyries` triedy `Rodinka`.

Ak chcete v pythone použiť knižnicu z [examples/sat](../../examples/sat), nemusíte
si ju kopírovať do aktuálneho adresára, stačí ak na začiatok svojej knižnice
pridáte:
```python
import os
import sys
sys.path[0:0] = [os.path.join(sys.path[0], os.path.join('..', '..', '..', 'examples', 'sat'))]
import sat
```

Odovzdávanie riešení v iných jazykoch konzultujte s cvičiacimi.
