%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for Cyberlogic        %
%                                           %
% Giselle Reis - 2019                       %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% N.B.: encoding for one principal K.

subexp r   lin.
subexp kr  lin.
subexp l   unb.
subexp kl  unb.
subexp res unb.

subexpctx r   single suc.
subexpctx kr  single suc.
subexpctx l   many ant.
subexpctx kl  many ant.
subexpctx res many ant.

subexprel r  < kr.
subexprel l  < kl.
subexprel kr < l.
subexprel kl < res.

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

% Attestation
not (lft (att A)) * ![kr] ?[l] (lft A).
not (rght (att A)) * ![l] ?[r] (rght A). % First bang for duality of rules

% Locality
not (lft (res A)) * ?[res] (lft A).
not (rght (res A)) * ![res] ?[r] (rght A).

% False
(not (lft false)) * top.

% True
(not (rght true)) * top.

rules axiom.
((not (lft A)) * (not (rght A))).

rules cut.
((![l] (?[r] (rght A))) * (?[l] (lft A))).

