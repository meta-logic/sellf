%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for G1m               %
%                                           %
% Giselle Machado Reis - 2012               %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l lin.
subexp r lin.

% Implication
%lft (imp a b) := ([l]bang ([r]? (rght a))) ,; ([l]? (lft b)).
%rght (imp a b) := ([l]bang (([l]? (lft a)) | ([r]? (rght b)))).

% Conjunction
lft (and a b) := ([l]? (lft a)) | ([l]? (lft b)).
rght (and a b) := ([l]bang ([r]? (rght a))) , ([l]bang ([r]? (rght b))).

% Disjunction
%lft (or a b) := ([l]? (lft a)) & ([l]? (lft b)).
%rght (or a b) := ([l]bang ([r]? (rght a))) ; ([l]bang ([r]? (rght b))).

% Forall
%lft (forall a) := [l]? (lft (a X)).
%rght (forall a) := [l]bang (pi \X ([r]? (rght (a X)))).

% Exists
%lft (exists a) := pi \X ([l]? (lft (a X))).
%rght (exists a) := [l]bang ([r]? (rght (a X))).

% axiom
%(not (lft a)) , (not (rght a)).
%(not (lft b)) , (not (rght b)).

% Cut rule
([l]bang ([r]? (rght a))) , ([l]? (lft a)).
([l]bang ([r]? (rght b))) , ([l]? (lft b)).

% Contraction left
%(not (lft a)) , ([l]? (lft a)) | ([l]? (lft a)).
%(not (lft b)) , ([l]? (lft b)) | ([l]? (lft b)).

% Weakening left
%(not (lft a)) , bot.
%(not (lft b)) , bot.

