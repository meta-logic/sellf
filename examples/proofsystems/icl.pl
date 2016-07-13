% Intuitionistic Control Logic (ICL)
% From: http://www.lix.polytechnique.fr/~dale/papers/iclconference.pdf
%
% Giselle Reis - 2012

subexp l unb.
subexp r unb.
subexp c lin. % holds the control formula

subexpctx l many ant.
subexpctx r many suc.
subexpctx c single suc.

subexprel c < l.
subexprel c < r.

rules introduction.
% Implication
not (lft  (imp A B)) * ![c] ?[c] (rght A) *  ?[l] (lft B).
not (rght (imp A B)) * ![c] (?[l] (lft A) | ?[c] (rght B)).

% Conjunction
not (lft  (and A B)) * ?[l] (lft A) | ?[l] (lft  B).
not (rght (and A B)) * ![c] ?[c] (rght A) * ![c] ?[c] (rght B).

% Disjunction
not (lft  (or A B)) * ?[l] (lft  A) & ?[l] (lft  B).
not (rght (or A B)) * ![c] ?[c] (rght A) + ![c] ?[c] (rght B).

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
?[l] (lft A) * ![c] ?[c] (rght A).
![c] ?[l] (lft A) * ?[c] (rght A).
