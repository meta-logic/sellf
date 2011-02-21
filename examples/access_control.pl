% Query: (checkPerm 3 finish) should return "Permission Denied".
% Query: (checkPerm 2 finish) should return "Permission granted.".

subexp un unb.
subexp pLoc aff.
subexp pAuxLoc aff.

subexprel pLoc <= un.
subexprel pAuxLoc <= un.

context pLoc.

perm 1.
perm 2.

context un.

checkPerm X Prog :- perm X, (pAux X [pAuxLoc] -o move (Prog "Yes")).
checkPerm X Prog :- perm Y, X <>Y, (pAux Y [pAuxLoc] -o checkPerm X Prog).
checkPerm X Prog :- [pLoc]hbang move (Prog "No").

move Prog :- pAux X, (perm X [pLoc]-o move Prog). 
move Prog :- [pAuxLoc]hbang Prog.

finish "Yes" :- print "Permission granted.".
finish "No" :- print "Permission denied!".
