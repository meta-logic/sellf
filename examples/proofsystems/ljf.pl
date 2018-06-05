%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for LJF               %
% (LJ with additive and multiplicative      %
% connectives)                              %
%                                           %
% Giselle Reis   -   2015                   %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Adequacy on the level of derivations

% The sequents will be Gamma |- Delta 
% where Gamma and Delta are multi-sets of formulas (linear)
% and Delta contains at most one formuls at all times.
% The fact that sometimes the context is copied and sometimes 
% it is split is encoded in the rules themselves.

subexp r lin.
subexp l lin.

subexpctx l many ant.
subexpctx r single suc.

rules introduction.

% Implication
not (lft (imp A B)) *  ![l] ?[r] (rght A) * ?[l] (lft B).
not (rght (imp A B)) *  ?[l] (lft A) | ![l] ?[r] (rght B).

% Disjunction
not (lft (or A B)) * ?[l] (lft A) & ?[l] (lft B).
not (rght (or A B)) * ![l] ?[r] (rght A) + ![l] ?[r] (rght B).

% Conjunction additive
not (lft (andA A B)) * ?[l] (lft A) + ?[l] (lft B).
not (rght (andA A B)) * ![l] ?[r] (rght A) & ![l] ?[r] (rght B).

% Conjunction multiplicative
not (lft (andM A B)) * ?[l] (lft A) | ?[l] (lft B).
not (rght (andM A B)) * ![l] ?[r] (rght A) * ![l] ?[r] (rght B).

rules axiom.
not (lft A) * not (rght A).

rules structural.
not (lft A) * ?[l] (lft A) | ?[l] (lft A). 
