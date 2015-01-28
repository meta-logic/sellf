%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for LK with           %
% additive and multiplicative connectives   %
%                                           %
% Giselle Reis   -   2015                   %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% The sequents will be Gamma |- Delta 
% where Gamma and Delta are multi-sets of formulas (linear).
% The fact that sometimes the context is copied and sometimes 
% it is split is encoded in the rules themselves.

subexp l lin.
subexp r lin.

subexpctx l many lft.
subexpctx r many rght.

rules introduction.

% Conjunction additive
(not (lft (andA A B))) * (([l]? (lft A)) + ([l]? (lft B))).
(not (rght (andA A B))) * (([r]? (rght A)) & ([r]? (rght B))).

% Conjunction multiplicative
(not (lft (andM A B))) * (([l]? (lft A)) | ([l]? (lft B))).
(not (rght (andM A B))) * (([r]? (rght A)) * ([r]? (rght B))).

% Disjunction additive
(not (lft (orA A B))) * (([l]? (lft A)) & ([l]? (lft B))).
(not (rght (orA A B))) * (([r]? (rght A)) + ([r]? (rght B))).

% Disjunction multiplicative
(not (lft (orM A B))) * (([l]? (lft A)) * ([l]? (lft B))).
(not (rght (orM A B))) * (([r]? (rght A)) | ([r]? (rght B))).

rules axiom.
((not (lft A)) * (not (rght A))).

