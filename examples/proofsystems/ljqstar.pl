%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for LJQ*              %
%                                           %
% Giselle Reis - 2012                       %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l unb.
subexp r unb.
subexp f lin.

subexprel r < l.

subexpctx l many ant.
subexpctx r many suc.
subexpctx f single suc.

rules axiom.
% Init
not (lft A) * not (?[f] rght A).

rules introduction.
% Implication
not (lft (imp A B)) * ![l] ?[f] (rght A) * ![r] ?[l] (lft B).
not (rght (imp A B)) * ![l] (?[l] (lft A) | ?[r] (rght B)).

% Disjunction
not (lft (or A B)) * ![r] ?[l] (lft A) * ![r] ?[l] (lft B).
not (rght (or A B)) * ![r] (?[r] (rght A) | ?[r] (rght B)).

% Conjunction
not (lft (and A B)) * ![r] (?[l] (lft A) | ?[l] (lft B)).
not (rght (and A B)) * ![r] ?[f] (rght A) * ![r] ?[f] (rght B).

% Bottom
%not (lft bottom).

% TODO: implement all cut rules

