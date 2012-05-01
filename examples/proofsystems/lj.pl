%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for LJ                %
%                                           %
% Elaine Pimentel   -   2012                %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp infty unb.
subexp r lin.

rules introduction.

% Implication
(not (lft (imp A B))) * (([r]? (rght A)) * ([infty]? (lft B))).
(not (rght (imp A B))) *  (([infty]? (lft A)) | ([r]? (rght B))).

% Conjunction
(not (lft (and A B))) * (([infty]? (lft A)) + ([infty]? (lft B))).
(not (rght (and A B))) * (([r]? (rght A)) & ([r]? (rght B))).

% Disjunction
(not (lft (or A B))) * (([infty]? (lft A)) & ([infty]? (lft B))).
(not (rght (or A B))) * (([r]? (rght A)) + ([r]? (rght B))).

% Forall
(not (lft (forall A))) * (sigma \X ([infty]? (lft (A X)))).
(not (rght (forall A))) *  (pi \X ([r]? (rght (A X)))).

% Exists
(not (lft (exists A))) * (pi \X ([infty]? (lft (A X)))).
(not (rght (exists A))) * (sigma \X ([r]? (rght (A X)))).

% False
(not (lft false)) * top.

% True
(not (rght true)) * top.

rules axiom.
sigma \A ((not (lft A)) * (not (rght A))).

rules cut.
sigma \A (([r]? (rght A)) * ([infty]? (lft A))).
