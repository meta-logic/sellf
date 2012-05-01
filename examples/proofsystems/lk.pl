%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for LK                %
%                                           %
% Elaine Pimentel   -   2012                %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rules introduction.

% Implication
(not (lft (imp A B))) * ((? (rght A)) * (? (lft B))).
(not (rght (imp A B))) *  ((? (lft A)) | (? (rght B))).

% Conjunction
(not (lft (and A B))) * ((? (lft A)) + (? (lft B))).
(not (rght (and A B))) * ((? (rght A)) & (? (rght B))).

% Disjunction
(not (lft (or A B))) * ((? (lft A)) & (? (lft B))).
(not (rght (or A B))) * ((? (rght A)) + (? (rght B))).

% Forall
(not (lft (forall A))) * (sigma \X (? (lft (A X)))).
(not (rght (forall A))) *  (pi \X (? (rght (A X)))).

% Exists
(not (lft (exists A))) * (pi \X (? (lft (A X)))).
(not (rght (exists A))) * (sigma \X (? (rght (A X)))).

% False
(not (lft false)) * top.

% True
(not (rght true)) * top.

rules axiom.
sigma \A ((not (lft A)) * (not (rght A))).

rules cut.
sigma \A ((? (rght A)) * (? (lft A))).
