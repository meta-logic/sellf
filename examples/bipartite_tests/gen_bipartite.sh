#!/bin/bash

graphs=$1

nodes=$2
#cut=$3

for i in `seq 1 $graphs`; do

file_name1=bipartite_${i}_${nodes}
file_name2=bipartite_cut_${i}_${nodes}

# Writing signature file
sig="
type node int -> o.\n
\rtype edge int -> int -> o.\n
\rtype auxE int -> int -> o.\n
\rtype auxN int  -> o.\n\n

\rtype colour int -> int -> o.\n\n

\rtype bipartite o.\n
\rtype colourN   int ->  tsub -> tsub -> o -> o.\n
\rtype moveE tsub -> o -> o.\n\n

\rtype tComponent tsub -> o.\n\n

\rtype tCustom o.\n
\rtype test o.\n" 
echo -e $sig > $file_name1.sig
echo -e $sig > $file_name2.sig

# Writing program file
s="
\rsubexp un unb.\n
\rsubexp snodes aff.\n
\rsubexp sedges aff.\n
\rsubexp scolour aff.\n\n

\r% All subexponentials are smaller than un.\n

\rsubexprel snodes <= un.\n
\rsubexprel sedges <= un.\n
\rsubexprel scolour <= un.\n\n

\rcontext snodes.\n\n
" 
echo -e $s > $file_name1.pl
echo -e $s > $file_name2.pl

for n in `seq 1 $nodes`; do
  echo -e "node $n." >> $file_name1.pl
  echo -e "node $n." >> $file_name2.pl
done

echo -e "\ncontext sedges.\n\n" >> $file_name1.pl
echo -e "\ncontext sedges.\n\n" >> $file_name2.pl

for j in `seq 1 $nodes`; do
  for k in `seq 1 $nodes`; do
    r1=$RANDOM
    r2=$RANDOM
    if [ $j -ne $k -a $r1 -gt $r2 ] ; then
      echo -e "edge $j $k." >> $file_name1.pl
      echo -e "edge $j $k." >> $file_name2.pl
    fi
  done
done

# Program without cut
echo -e "
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

colourN X SN SE Prog :- edge X Z, colour X CX, colour Z CX,  print \"The graph is not bipartite!\".
colourN X SN SE Prog :- edge Z X, colour X CX, colour Z CX,  print \"The graph is not bipartite!\".

% All neighbors of a node have been checked as all edges of the graph have been traversed. Hence, move the edges from 
% auxE back to edges.

colourN X SN SE Prog :- [sedges]hbang moveE SE Prog.

% Move the contents of the context sauxE to sedges.

moveE SE Prog :- auxE X Y, edge X Y [sedges]-o moveE SE Prog.
moveE SE Prog :- [SE]hbang Prog.
" >> $file_name1.pl

# Program with cut
echo -e "
context un.

% In the program below, 1 is blue and 0 is red.

% Pick non-deterministically a node in a new component of the graph. If all nodes have been picked, then 
% it means that the graph is bipartite.

bipartite :- {node X}, nsub \S1 (colour X 1 [scolour]-o  (auxN X  [S1]-o tComponent S1)).
bipartite :- [snodes]hbang one. 

% Traverse a component of the graph.

tComponent S1 :- {auxN X}, nsub \S2 (colourN X S1 S2 (tComponent S1)).
tComponent S1 :- [S1]hbang bipartite.

% Find a neighbor of X. If it does not have a colour, then assign the correct colour and insert them in 
% auxN, so that it is picked later.

colourN X SN SE Prog :- {edge X Z, colour X 1, node Z}, 
                      colour X 1 [scolour]-o (colour Z 0 [scolour]-o (auxN Z  [SN]-o (auxE X Z [SE]-o colourN X SN SE Prog))).

colourN X SN SE Prog :- {edge X Z, colour X 0, node Z}, 
                      colour X 0 [scolour]-o (colour Z 1 [scolour]-o (auxN Z  [SN]-o (auxE X Z [SE]-o colourN X SN SE Prog))).

colourN X SN SE Prog :- {edge Z X, colour X 1, node Z}, 
                    colour X 1 [scolour]-o (colour Z 0 [scolour]-o (auxN Z  [SN]-o (auxE Z X [SE]-o colourN X SN SE Prog))).

colourN X SN SE Prog :- {edge Z X, colour X 0, node Z}, 
                    colour X 0 [scolour]-o (colour Z 1 [scolour]-o (auxN Z  [SN]-o (auxE Z X [SE]-o colourN X SN SE Prog))).

% Find a neighbor of X. If it has a different colour, then it means that it was already picked at some moment. Hence, 
% proceed without the need to pick this node later.

colourN X SN SE Prog :- {edge X Z, colour X CX, colour Z CZ, CX <> CZ}, 
                      colour X CX [scolour]-o (colour Z CZ [scolour]-o (auxE X Z [SE]-o colourN X SN SE Prog)).

colourN X SN SE Prog :- {edge Z X, colour X CX, colour Z CZ, CX <> CZ}, 
                    colour X CX [scolour]-o (colour Z CZ [scolour]-o (auxE Z X [SE]-o colourN X SN SE Prog)).

% If one picks an edge that is not connected to X, then just move it to sauxE.

colourN X SN SE Prog :- {edge Y Z, X <> Y, Z <> X}, (auxE Y Z [SE]-o colourN X SN SE Prog).

% Find a neighbor of X, if it has a the same colour, then it means that the graph is not bipartite.

colourN X SN SE Prog :- {edge X Z, colour X CX, colour Z CX},  print \"The graph is not bipartite!\".
colourN X SN SE Prog :- {edge Z X, colour X CX, colour Z CX},  print \"The graph is not bipartite!\".

% All neighbors of a node have been checked as all edges of the graph have been traversed. Hence, move the edges from 
% auxE back to edges.

colourN X SN SE Prog :- [sedges]hbang moveE SE Prog.

% Move the contents of the context sauxE to sedges.

moveE SE Prog :- auxE X Y, edge X Y [sedges]-o moveE SE Prog.
moveE SE Prog :- [SE]hbang Prog.
" >> $file_name2.pl

done
