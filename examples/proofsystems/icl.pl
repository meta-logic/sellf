% Intuitionistic Control Logic (ICL)
% From: http://www.lix.polytechnique.fr/~dale/papers/iclconference.pdf
%
% Giselle Reis - 2012

subexp r lin.

subexpctx r single suc.

rules introduction.
% Implication
not (lft  (imp A B)) * ! ?[r] (rght A) *  ? (lft B).
not (rght (imp A B)) * ! (? (lft A) | ?[r] (rght B)).

% Conjunction
not (lft  (and A B)) * ? (lft A) | ? (lft  B).
not (rght (and A B)) * ! ?[r] (rght A) * ! ?[r] (rght B).

% Disjunction
not (lft  (or A B)) * ? (lft  A) & ? (lft  B).
not (rght (or A B)) * ! ?[r] (rght A) + ! ?[r] (rght B).

% True
not (rght tt) * top.

% False : zz (zero)
not (lft zz) * top.

% False : bttm (bottom)
not (lft bttm) * one.

rules axiom.
% Init
not (lft A) * not (rght A).

rules cut.
% Cut
? (lft A) * ! ?[r] (rght A).
! ? (lft A) * ?[r] (rght A).
