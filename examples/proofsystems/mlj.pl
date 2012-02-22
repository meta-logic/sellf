%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for mLJ               %
%                                           %
% Giselle Machado Reis - 2012               %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l unb.
subexp r unb.

% Implication
lft (imp A B) := ([r]? (rght A)) , ([l]? (lft B)).
rght (imp A B) := [l]bang ( ([l]? (lft A)) | ([r]? (rght B))).

% Conjunction
lft (and A B) := ([l]? (lft A)) | ([l]? (lft B)).
rght (and A B) := ([r]? (rght A)) , ([r]? (rght B)).

% Disjunction
lft (or A B) := ([l]? (lft A)) , ([l]? (lft B)).
rght (or A B) := ([r]? (rght A)) | ([r]? (rght B)).

% Forall
lft (forall A) := [l]? (lft (A X)).
rght (forall A) := [l]bang (pi \X ([r]? (rght (A X)))).

% Exists
lft (exists A) := pi \X ([l]? (lft (A X))).
rght (exists A) := [r]? (rght (A X)).

% Bottom
%(not (lft bottom)).

% Axiom
(not (lft (A))) , (not (rght (A))).

% Cut rule
%([l]? (lft A)) , ([r]? (rght A)).
