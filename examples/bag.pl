load1 X Sub Prog :- tup1 X Sub [Sub]-o Prog.
load2 X Y Sub Prog :- tup2 X Y Sub [Sub]-o Prog.

unload1 X Sub KProg :- tup1 X Sub, (KProg X).
unload2 X Y Sub KProg :- tup2 X Y Sub, (KProg X Y).

while (eq X X) KProg Prog :- KProg (while (eq X Y) KProg Prog).
while (eq X Y) KProg Prog :- X > Y, Prog.
while (eq X Y) KProg Prog :- X < Y, Prog.

while (neq X Y) KProg Prog :- X <> Y, KProg (while (eq X Y) KProg Prog).
while (neq X X) KProg Prog :- Prog.

while (less X Y) KProg Prog :- X < Y, KProg (while (eq X Y) KProg Prog).
while (less X Y) KProg Prog :- X >= Y, Prog.

while (grt X Y) KProg Prog :- X > Y, KProg (while (eq X Y) KProg Prog).
while (grt X Y) KProg Prog :- X <= Y, Prog.

while (leq X Y) KProg Prog :- X <= Y, KProg (while (eq X Y) KProg Prog).
while (leq X Y) KProg Prog :- X > Y, Prog.

while (geq X Y) KProg Prog :- X >= Y, KProg (while (eq X Y) KProg Prog).
while (geq X Y) KProg Prog :- X < Y, Prog.

loop1 Sub KProg Prog :- tup1 X Sub, KProg X (loop1 Sub KProg Prog).  
loop1 Sub KProg Prog :- [Sub]bang Prog.

loop2 Sub KProg Prog :- tup2 X Y Sub, KProg X Y (loop2 Sub KProg Prog).   
loop2 Sub KProg Prog :- [Sub]bang Prog.

paral Prog1 Prog2 :- Prog1.
paral Prog1 Prog2 :- Prog2.

if (eq X X) Prog :- Prog. 
if (neq X Y) Prog :- X <> Y, Prog.
if (less X Y) Prog :- X < Y, Prog.
if (grt X Y) Prog :- X > Y, Prog.
if (leq X Y) Prog :- X <= Y, Prog.
if (geq X Y) Prog :- X >= Y, Prog.
if (isEmpty Sub) Prog :- [Sub]hbang Prog.

new Prog :- nsub \X (Prog X).



