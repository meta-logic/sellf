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

% Implication
%lft (imp A B) := ([l]bang ([r]? (rght A))) , ([l]? (lft B)).
%rght (imp A B) := [l]bang (([l]? (lft A)) | ([r]? (rght B))).

% Conjunction
lft (and A B) := ([l]? (lft A)) | ([l]? (lft B)).
rght (and A B) := ([l]bang ([r]? (rght A))) , ([l]bang ([r]? (rght B))).
%lft (and A B) := (lft A).
%rght (and A B) := (rght B).

% Disjunction
%lft (or A B) := ([l]? (lft A)) & ([l]? (lft B)).
%rght (or A B) := ([l]bang ([r]? (rght A))) ; ([l]bang ([r]? (rght B))).

% Forall
%lft (forall A) := [l]? (lft (A X)).
%rght (forall A) := [l]bang (pi \X ([r]? (rght (A X)))).

% Exists
%lft (exists A) := pi \X ([l]? (lft (A X))).
%rght (exists A) := [l]bang ([r]? (rght (A X))).

% Axiom
%(not (lft A)) , (not (rght A)).

% Cut rule
sigma \A ([l]bang ([r]? (rght A))) , ([l]? (lft A)).

% Contraction left
%not (lft A) , ([l]? (lft A)) | ([l]? (lft A)).

% Weakening left
%not (lft A) , bot.

