subexp un unb.
subexp slft unb.
subexp srght unb.

subexprel slft <= un.
subexprel srght <= un.

context un.


solve :- rght F,  lft F.

solve :- lft (imp F1 F2), (rght F1 [srght]-o solve), (lft F2 [slft]-o solve).
solve :- rght (imp F1 F2), [srght]hbang(lft F1 [slft]-o (rght F2 [srght]-o solve)).

solve :- lft (and F1 F2),  lft F1 [slft]-o (lft F2 [slft]-o solve).
solve :- rght (and F1 F2),  (rght F1 [srght]-o solve), (rght F2 [srght]-o solve).