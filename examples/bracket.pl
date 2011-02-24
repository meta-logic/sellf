subexp u unb.
subexp l lin.

context l.

data 1.
data 2.

context u.

pred Prog :- {data X}, Prog X.
finish X :- X = 1, print "Chose 1".
