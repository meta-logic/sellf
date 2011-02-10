subexp un unb.
subexp as lin.
subexp aux lin.
subexprel aux <= un.

context as.

perm 1.

context un.

check X :-  perm Y, Y < X, (pAux Y [aux]-o check X).
check X :-  perm Y, X < Y, (pAux Y [aux]-o check X).

%check X :-  perm X.

check X :- [aux]bang del.   

del :- pAux X, del.

del :- [un]bang one.
