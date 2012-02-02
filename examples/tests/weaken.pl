subexp un unb.
subexp ln lin.
subexp lnD lin.
subexp lnDD lin.


subexprel ln <= lnD.
subexprel lnD <= lnDD.

context ln.

%g 1.

context lnD.

g 2.

context un.

test X :-  [ln]bang g X.
