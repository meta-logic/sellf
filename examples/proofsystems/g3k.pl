%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for G3k               %
%                                           %
% Giselle Reis - 2012                       %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l unb.
subexp r unb.
subexp rr unb.

subexpctx l many ant.
subexpctx r many suc.

rules introduction.

% Conjunction
not (mlft (and A B) X) * ?[l] (mlft A X) | ?[l] (mlft B X).
not (mrght (and A B) X) * ?[r] (mrght A X) * ?[r] (mrght B X).

% Disjunction
not (mlft (or A B) X) * ?[l] (mlft A X) * ?[l] (mlft B X).
not (mrght (or A B) X) * ?[r] (mrght A X) | ?[r] (mrght B X).

% Implication
not (mlft (imp A B) X) * ?[r] (mrght A X) * ?[l] (mlft B X).
not (mrght (imp A B) X) * ?[l] (mlft A X) | ?[r] (mrght B X).

% Necessarely
not (mlft (nec A) X) * exs Y ( ![rr] not (relation X Y) * ?[l] (mlft A Y) ).
not (mrght (nec A) X) * all Y ( ?[rr] (relation X Y) | ?[r] (mrght A Y) ).

% Possibly
not (mlft (poss A) X) * all Y ( ?[rr] (relation X Y) | ?[l] (mlft A Y) ).
not (mrght (poss A) X) * exs Y ( ![rr] not (relation X Y) * ?[r] (mrght A Y) ).

rules axiom.
not (mlft A X) * not (mrght A X).

rules cut.
% What is cut??
?[r] (mrght A X) * ?[l] (mlft A X).

rules structural.
% Reflexivity
not (relation X X).

% Symmetry
not (relation X Y) * not (relation X Y).

% Transitivity
not (relation X Y) * not (relation Y Z) * (relation X Z).

% Euclidian
not (relation X Y) * not (relation X Z) * (relation Y Z).


