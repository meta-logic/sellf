%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for G3k               %
%                                           %
% Giselle Machado Reis - 2012               %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l unb.
subexp r unb.
subexp rr unb.

rules introduction.

% Conjunction
(not (lft (pair (X (and A B))))) * ([l]? (lft (pair X A))) | ([l]? (lft (pair X B))).
(not (rght (pair (X (and A B))))) * ( ([r]? (rght (pair X A))) * ([r]? (rght (pair X B)))).

% Disjunction
(not (lft (pair (X (or A B))))) * (([l]? (lft (pair X A))) * ([l]? (lft (pair X B)))).
(not (rght (pair (X (or A B))))) * ( ([r]? (rght (pair X A))) | ([r]? (rght (pair X B)))).

% Implication
(not (lft (pair (X (imp A B))))) * (([r]? (lft (pair X A))) * ([l]? (lft (pair X B)))).
(not (rght (pair (X (imp A B))))) * ( ([l]? (rght (pair X A))) | ([r]? (rght (pair X B)))).

% Necessarely
(not (lft (pair (X (nec A))))) * sigma \Y ( ([rr]bang (not (relation X Y))) * ([l]? (lft (pair Y A)) ) ).
(not (rght (pair (X (nec A))))) * pi \Y ( ([rr]? (relation X Y)) | ([r]? (rght (pair Y A)) ) ).

% Possibly
(not (lft (pair (X (poss A))))) * pi \Y ( ([rr]? (relation X Y)) | ([l]? (lft (pair Y A)) ) ).
(not (rght (pair (X (poss A))))) * sigma \Y ( ([rr]bang (not (relation X Y))) * ([r]? (rght (pair Y A)) ) ).

rules axiom.
((not (lft (pair X A))) * (not (rght (pair X A)))).

rules cut.
% What is cut??
%([l]bang ([r]? (rght A))) * ([l]? (lft A)).

rules structural.
% Reflexivity
(not (relation X X)).

% Symmetry
(not (relation X Y)) * (not (relation X Y)).

% Transitivity
(not (relation X Y)) * (not (relation Y Z)) * (relation X Z).

% Euclidian
(not (relation X Y)) * (not (relation X Z)) * (relation Y Z).


