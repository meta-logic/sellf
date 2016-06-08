%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for G1m               %
%                                           %
% Giselle Reis - 2012                       %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l lin.
subexp r lin.

subexprel r < l.

subexpctx l many ant.
subexpctx r single suc.

rules introduction.

% Implication
not (lft (imp A B)) * ![l] ?[r] (rght A) * ?[l] (lft B).
not (rght (imp A B)) * ![l] (?[l] (lft A) | ?[r] (rght B)).

% Conjunction
not (lft (and A B)) * ?[l] (lft A) | ?[l] (lft B).
not (rght (and A B)) * ![l] ?[r] (rght A) * ![l] ?[r] (rght B).

% Disjunction
not (lft (or A B)) * ?[l] (lft A) & ?[l] (lft B).
not (rght (or A B)) * ![l] ?[r] (rght A) + ![l] ?[r] (rght B).

rules axiom.
not (lft A) * not (rght A).

rules cut.
![l] ?[r] (rght A) * ?[l] (lft A).

rules structural.
% Contraction left
not (lft A) * ?[l] (lft A) | ?[l] (lft A).

% Weakening left
not (lft A) * bot.

