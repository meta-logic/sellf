%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for G1m               %
%                                           %
% Giselle Machado Reis - 2012               %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l lin.
subexp r lin.

subexprel r < l.

subexpctx l many lft.
subexpctx r single rght.

rules introduction.

% Implication
(not (lft (imp A B))) * (([l]bang ([r]? (rght A))) * ([l]? (lft B))).
(not (rght (imp A B))) * [l]bang (([l]? (lft A)) | ([r]? (rght B))).

% Conjunction
(not (lft (and A B))) * ([l]? (lft A)) | ([l]? (lft B)).
(not (rght (and A B))) * (([l]bang ([r]? (rght A))) * ([l]bang ([r]? (rght B)))).

% Disjunction
(not (lft (or A B))) * ([l]? (lft A)) & ([l]? (lft B)).
(not (rght (or A B))) * ([l]bang ([r]? (rght A))) + ([l]bang ([r]? (rght B))).

% Forall
%(not (lft (forall A))) * sigma \X ([l]? (lft (A X))).
%(not (rght (forall A))) * [l]bang (pi \X ([r]? (rght (A X)))).

% Exists
%(not (lft (exists A))) * pi \X ([l]? (lft (A X))).
%(not (rght (exists A))) * sigma \X ([l]bang ([r]? (rght (A X)))).

rules axiom.
((not (lft A)) * (not (rght A))).

rules cut.
([l]bang ([r]? (rght A))) * ([l]? (lft A)).

rules structural.
% Contraction left
(not (lft A) * ([l]? (lft A)) | ([l]? (lft A))).

% Weakening left
(not (lft A) * bot).

