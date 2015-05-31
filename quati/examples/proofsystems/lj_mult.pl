%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                             %
% SELLF specification for LJ  %
% (purely multiplicative      %
%  calculus)                  %
%                             %
% Giselle Machado Reis - 2013 %
%                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


subexp r lin.
subexp l lin.

subexpctx r unit rght.
subexpctx l many lft.

rules introduction.

% Implication
(not (lft (imp A B))) * (([l]bang ([r]? (rght A))) * ([l]? (lft B))).
(not (rght (imp A B))) *  (([l]? (lft A)) | ([r]? (rght B))).

% Conjunction
(not (lft (and A B))) * (([l]? (lft A)) + ([l]? (lft B))).
(not (rght (and A B))) * (([r]? (rght A)) * ([r]? (rght B))).

% Disjunction
(not (lft (or A B))) * (([l]? (lft A)) * ([l]? (lft B))).
(not (rght (or A B))) * (([r]? (rght A)) + ([r]? (rght B))).

% Forall
(not (lft (forall A))) * (sigma \X ([l]? (lft (A X)))).
(not (rght (forall A))) *  (pi \X ([r]? (rght (A X)))).

% Exists
(not (lft (exists A))) * (pi \X ([l]? (lft (A X)))).
(not (rght (exists A))) * (sigma \X ([r]? (rght (A X)))).

% Not
(not (lft (myNot A))) * ([l]bang ([r]? (rght A))).
(not (rght (myNot A))) * ([l]? (lft A)).

rules axiom.
((not (lft A)) * (not (rght A))).

rules cut.
(([r]? (rght A)) * ([l]? (lft A))).

rules structural.
(not (lft A)) * (([l]? (lft A)) | ([l]? (lft A)) ). 
(not (lft A)) * bot. 
