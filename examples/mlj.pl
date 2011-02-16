subexp un unb.
subexp slft unb.
subexp srght unb.

subexprel slft <= un.
subexprel srght <= un.

context un.

right F :- left F.

left (imp F1 F2) :- (right F1 [srght]-o solve), (left F2 [slft]-o solve).
right (imp F1 F2) :- left F1 [slft]-o (right F2 [srght]-o solve).

left (and F1 F2) :-  left F1 [slft]-o (left F2 [slft]-o solve).
right (and F1 F2) :- (right F1 [srght]-o solve), (right F2 [srght]-o solve).