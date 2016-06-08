%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for mLJ               %
%                                           %
% Giselle Reis - 2012                       %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l unb.
subexp r unb.

subexpctx l many ant.
subexpctx r many suc.

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

% Bottom
(not (lft bottom)).

rules axiom.
% Axiom
((not (lft (A))) * (not (rght (A)))).

rules cut.
% Cut rule
(([l]? (lft A)) * ([r]? (rght A))).

rules structural.
((not (lft A)) * ([l]? (lft A))).

