% Just run "lparse sound.pl | smodels 0"
% and smodels will return all the minimal models of the program below.

in(X, S) :- in(X, S1), union(S1, S2, S), form(X). 
in(X, S) :- in(X, S2), union(S1, S2, S), form(X).
1 {in(X, S1), in(X, S2)} 1  :- in(X, S),  union(S1, S2, S), form(X).

:- in(F, X), emp(X), form(F). 

:- in(F1, Ctx),  not equ(F, F1), form(F1), elin(F, Ctx).
in(F, Ctx) :- elin(F, Ctx). 

in(F, Ctx) :- mctx(F, Ctx).

form(a).
form(b).

equ(b, b).
equ(a, a). 

emp(ctxRprime). 
emp(ctxLprime). 
mctx(a, ctxU).
elin(b, ctxF).
emp(ctxLtwoprimes). 
union(ctxR, ctxF, ctxR1).
union(ctxRprime, ctxRtwoprimes, ctxR1).
union(ctxLprime, ctxLtwoprimes, ctxL). 

