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
(not (lft (andNeg A B))) * (([l]? (lft A)) + ([l]? (lft B))).
(not (rght (andNeg A B))) * (([r]? (rght A)) & ([r]? (rght B))).

% Conjunction multiplicative
(not (lft (andPos A B))) * (([l]? (lft A)) | ([l]? (lft B))).
(not (rght (andPos A B))) * (([r]? (rght A)) * ([r]? (rght B))).

% Disjunction additive
(not (lft (orPos A B))) * (([l]? (lft A)) & ([l]? (lft B))).
(not (rght (orPos A B))) * (([r]? (rght A)) + ([r]? (rght B))).

% Disjunction multiplicative
(not (lft (orNeg A B))) * (([l]? (lft A)) * ([l]? (lft B))).
(not (rght (orNeg A B))) * (([r]? (rght A)) | ([r]? (rght B))).

rules axiom.
((not (lft A)) * (not (rght A))).

