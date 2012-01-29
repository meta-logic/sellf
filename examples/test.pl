subexp as lin.
subexp bs lin.
subexp un unb.

context as.

b 1.
b 2.
b 3.

context un.

a :- b X.
a :- b X , Y is 3, b Y.
c :- b X.
d :- b X.
test :- a , c, d.

