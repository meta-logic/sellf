% Djikstra s shortest path algorithm. 

% We do not implement Fibonacci heaps here to improve the complexity of the algorithm
% However, this could be easily implemented using linear logic atoms linked by constants. 

subexp un unb.
subexp snodes aff.
subexp sedges aff.
subexp sauxN aff.
subexp sauxE aff.
subexp sdist aff.
subexp spicked aff.

% All subexponentials are smaller than un.

subexprel snodes <= un.
subexprel sedges <= un.
subexprel sauxN <= un.
subexprel sauxE <= un.
subexprel sdist <= un.
subexprel spicked <= un.

context snodes.

node 1.
node 2.
%node 3.
%node 4.
%node 5.

context sedges.

edge 1 2 10.
%edge 2 1.
%edge 2 3.
%edge 3 2.
%edge 1 3.
%edge 4 5.
%edge 5 4.

context un.

% In the program below, 1 is blue and 0 is red.

% Pick the source of the graph and assign it the distance 0.

djikstra Src :- node Src, (pickN Src 0 [spicked]-o  comp).

comp :- pickN X D1, (pickN X D1 [spicked]-o findMinAux X D1).
comp :- [spicked]hbang one, printD.

printD :- dist X D, print X D, printD.
printD :- [sdist]hbang one.

% Find the minium distance that still has to be picked. Here one could replace 
% these clauses by clauses that maintain a Fibonacci heap.

findMinAux X D1 :- pickN X D1, pickN Y D2, D1 <= D2, (auxN Y D2 [sauxN]-o (pickN X D1 [spicked]-o findMinAux X D1)).
findMinAux X D1 :- pickN X D1, pickN Y D2, D1 > D2, (auxN X D1 [sauxN]-o (pickN Y D2 [spicked]-o findMinAux Y D2)).
findMinAux X D1 :- pickN X D1, [spicked]hbang (dist X D1 [sdist]-o moveN (comDistN X comp)).

% Find a neighbor of X. If it does not have a distance assigned to it, then assign to it a distance. Place it 
% as well in sauxN so that it is picked later to traverse the graph.

comDistN X Prog :- edge X Y D1, dist X D2, node Y,  Z is D1 + D2, 
                             dist X D2 [sdist]-o (pickN Y Z [spicked]-o  (auxE X Y D1 [sauxE]-o comDistN X Prog)).

% Find a neighbor of X. If it has a distance assigned to it, then check whether we found a shorter distance. 

comDistN X Prog :- edge X Y D1, dist X D2, dist Y D3,  D3 <= D1 + D2, 
                             dist X D2 [sdist]-o  (auxN Y D3 [sauxN]-o  (auxE X Y D1 [sauxE]-o comDistN X Prog)).

comDistN X Prog :- edge X Y D1, dist X D2, dist Y D3,  D3 > D1 + D2, D4 is D1 + D2,
                             dist X D2 [sdist]-o  (auxN Y D4 [sauxN]-o  (auxE X Y D1 [sauxE]-o comDistN X Prog)).

comDistN X Prog :- edge Y Z D1, Y<>X,
                              (auxE X Y D1 [sauxE]-o comDistN X Prog).


comDistN X Prog :- [sedges]hbang moveE Prog.


moveN Prog :- auxN X D, pickN X D [spicked]-o moveN Prog.
moveN Prog :- [sauxN]hbang Prog.

moveE Prog :- auxE X Y D, edge X Y D [sedges]-o moveE Prog.
moveE Prog :- [sauxE]hbang Prog.
