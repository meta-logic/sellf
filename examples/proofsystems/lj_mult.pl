%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for LJ                %
% (purely multiplicative calculus)          %
%                                           %
% Giselle Reis   -   2013                   %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp r lin.
subexp l lin.

subexpctx l many ant.
subexpctx r single suc.

rules introduction.

% Implication
not (lft (imp A B)) * ![l] ?[r] (rght A) * ?[l] (lft B).
not (rght (imp A B)) *  ?[l] (lft A) | ?[r] (rght B).

% Conjunction
not (lft (and A B)) * ?[l] (lft A) | ?[l] (lft B).
not (rght (and A B)) * ?[r] (rght A) * ?[r] (rght B).

% Disjunction
not (lft (or A B)) * ?[l] (lft A) & ?[l] (lft B).
not (rght (or A B)) * ?[r] (rght A) + ?[r] (rght B).

% Forall
not (lft (forall A)) * exs X ?[l] (lft (A X)).
not (rght (forall A)) * all X ?[r] (rght (A X)).

% Exists
not (lft (exists A)) * all X ?[l] (lft (A X)).
not (rght (exists A)) * exs X ?[r] (rght (A X)).

% Not
not (lft (myNot A)) * ![l] ?[r] (rght A).
not (rght (myNot A)) * ?[l] (lft A).

rules axiom.
not (lft A) * not (rght A).

rules cut.
?[r] (rght A) * ?[l] (lft A).

rules structural.
not (lft A) * ?[l] (lft A) | ?[l] (lft A). 
not (lft A) * bot. 
not (rght A) * bot.

