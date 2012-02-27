%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for mLJ               %
%                                           %
% Giselle Machado Reis - 2012               %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l unb.
subexp r unb.

rules introduction.
% Implication
(not (lft (imp A B))) * (([r]? (rght A)) * ([l]? (lft B))).
(not (rght (imp A B))) * [l]bang ( ([l]? (lft A)) | ([r]? (rght B))).

% Conjunction
(not (lft (and A B))) * ([l]? (lft A)) | ([l]? (lft B)).
(not (rght (and A B))) * (([r]? (rght A)) * ([r]? (rght B))).

% Disjunction
(not (lft (or A B))) * (([l]? (lft A)) * ([l]? (lft B))).
(not (rght (or A B))) * ([r]? (rght A)) | ([r]? (rght B)).

% Forall
(not (lft (forall A))) * [l]? (lft (A X)).
(not (rght (forall A))) * [l]bang (pi \X ([r]? (rght (A X)))).

% Exists
(not (lft (exists A))) * pi \X ([l]? (lft (A X))).
(not (rght (exists A))) * [r]? (rght (A X)).

rules axiom.
% Bottom
(not (lft bottom)).

% Axiom
(not (lft (A))) * (not (rght (A))).

rules cut.
% Cut rule
([l]? (lft A)) * ([r]? (rght A)).
