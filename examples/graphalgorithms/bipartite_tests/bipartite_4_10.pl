subexp un unb.
 subexp snodes aff.
 subexp sedges aff.
 subexp scolour aff.

 % All subexponentials are smaller than un.
 subexprel snodes <= un.
 subexprel sedges <= un.
 subexprel scolour <= un.

 context snodes.


node 1.
node 2.
node 3.
node 4.
node 5.
node 6.
node 7.
node 8.
node 9.
node 10.

context sedges.


edge 1 2.
edge 1 3.
edge 1 4.
edge 1 9.
edge 1 10.
edge 2 4.
edge 3 4.
edge 3 5.
edge 3 6.
edge 3 8.
edge 4 3.
edge 4 5.
edge 4 6.
edge 4 8.
edge 4 10.
edge 5 4.
edge 5 6.
edge 5 8.
edge 5 9.
edge 5 10.
edge 6 1.
edge 6 3.
edge 6 4.
edge 6 5.
edge 6 7.
edge 6 9.
edge 7 8.
edge 7 10.
edge 8 6.
edge 8 7.
edge 9 6.
edge 9 8.
edge 9 10.
edge 10 1.
edge 10 2.
edge 10 3.
edge 10 5.
edge 10 7.
edge 10 9.

context un.

% In the program below, 1 is blue and 0 is red.

% Pick non-deterministically a node in a new component of the graph. If all nodes have been picked, then 
% it means that the graph is bipartite.

bipartite :- node X, nsub \S1 (colour X 1 [scolour]-o  (auxN X  [S1]-o tComponent S1)).
bipartite :- [snodes]hbang one. 

% Traverse a component of the graph.

tComponent S1 :- auxN X,  nsub \S2 (colourN X S1 S2 (tComponent S1)).
tComponent S1 :- [S1]hbang bipartite.

% Find a neighbor of X. If it does not have a colour, then assign the correct colour and insert them in 
% auxN, so that it is picked later.

colourN X SN SE Prog :- edge X Z, colour X 1, node Z, 
                      colour X 1 [scolour]-o (colour Z 0 [scolour]-o (auxN Z  [SN]-o (auxE X Z [SE]-o colourN X SN SE Prog))).

colourN X SN SE Prog :- edge X Z, colour X 0, node Z, 
                      colour X 0 [scolour]-o (colour Z 1 [scolour]-o (auxN Z  [SN]-o (auxE X Z [SE]-o colourN X SN SE Prog))).

colourN X SN SE Prog :- edge Z X, colour X 1, node Z, 
                    colour X 1 [scolour]-o (colour Z 0 [scolour]-o (auxN Z  [SN]-o (auxE Z X [SE]-o colourN X SN SE Prog))).

colourN X SN SE Prog :- edge Z X, colour X 0, node Z, 
                    colour X 0 [scolour]-o (colour Z 1 [scolour]-o (auxN Z  [SN]-o (auxE Z X [SE]-o colourN X SN SE Prog))).

% Find a neighbor of X. If it has a different colour, then it means that it was already picked at some moment. Hence, 
% proceed without the need to pick this node later.

colourN X SN SE Prog :- edge X Z, colour X CX, colour Z CZ, CX <> CZ, 
                      colour X CX [scolour]-o (colour Z CZ [scolour]-o (auxE X Z [SE]-o colourN X SN SE Prog)).

colourN X SN SE Prog :- edge Z X, colour X CX, colour Z CZ, CX <> CZ, 
                    colour X CX [scolour]-o (colour Z CZ [scolour]-o (auxE Z X [SE]-o colourN X SN SE Prog)).

% If one picks an edge that is not connected to X, then just move it to sauxE.

colourN X SN SE Prog :- edge Y Z, X <> Y, Z <> X, (auxE Y Z [SE]-o colourN X SN SE Prog).

% Find a neighbor of X, if it has a the same colour, then it means that the graph is not bipartite.

%colourN X SN SE Prog :- edge X Z, colour X CX, colour Z CX,  print "The graph is not bipartite!".
%colourN X SN SE Prog :- edge Z X, colour X CX, colour Z CX,  print "The graph is not bipartite!".

% All neighbors of a node have been checked as all edges of the graph have been traversed. Hence, move the edges from 
% auxE back to edges.

colourN X SN SE Prog :- [sedges]hbang moveE SE Prog.

% Move the contents of the context sauxE to sedges.

moveE SE Prog :- auxE X Y, edge X Y [sedges]-o moveE SE Prog.
moveE SE Prog :- [SE]hbang Prog.

