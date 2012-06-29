%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for GK                %
% (for Paraconsistent Logics)               %
%                                           %
% Giselle Machado Reis - 2012               %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l unb.
subexp r unb.

rules introduction.

% Conjunction
(not (lft (and A B))) * (([l]? (lft A)) | ([l]? (lft B))).
(not (rght (and A B))) * (([r]? (rght A)) * ([r]? (rght B))).

% Disjunction
(not (lft (or A B))) * (([l]? (lft A)) * ([l]? (lft B))).
(not (rght (or A B))) * (([r]? (rght A)) | ([r]? (rght B))).

% Implication
(not (lft (imp A B))) * (([r]? (rght A)) * ([l]? (lft B))).
(not (rght (imp A B))) *  (([l]? (lft A)) | ([r]? (rght B))).

% Negation
(not (lft (gkneg A))) * ([l]? (lft A)).

% Consistent
(not (lft (cons A))) * (([r]? (rght A)) * ([r]? (rght (gkneg A)))).
(not (rght (cons A))) * (([l]? (lft A)) | ([l]? (lft (gkneg A)))).

% TODO: Implement the negated rules

rules axiom.
((not (lft A)) * (not (rght A))).

rules cut.
(([r]? (rght A)) * ([l]? (lft A))).
