subexp u unb.
subexp l unb.

context l.

data 1.
data 2.

context u.

finish X :- data X.

pred Y :-  finish 2.

pred Y :-  finish 3.
pred Y :-  finish 3.
