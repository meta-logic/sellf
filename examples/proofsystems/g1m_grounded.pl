%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for G1m               %
%                                           %
% Giselle Machado Reis - 2012               %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l lin.
subexp r lin.

subexprel r < l.

subexpctx l many ant.
subexpctx r single suc.

rules introduction.
% Implication
(not (lft (imp a b))) * ([l]bang ([r]? (rght a))) * ([l]? (lft b)).
(not (rght (imp a b))) * ([l]bang (([l]? (lft a)) | ([r]? (rght b)))).

% Conjunction
(not (lft (and a b))) * ([l]? (lft a)) | ([l]? (lft b)).
(not (rght (and a b))) * ([l]bang ([r]? (rght a))) * ([l]bang ([r]? (rght b))).

% Disjunction
(not (lft (or a b))) * ([l]? (lft a)) & ([l]? (lft b)).
(not (rght (or a b))) * ([l]bang ([r]? (rght a))) + ([l]bang ([r]? (rght b))).

rules axiom.
(not (lft a)) * (not (rght a)).
(not (lft b)) * (not (rght b)).

rules cut.
([l]bang ([r]? (rght a))) * ([l]? (lft a)).
([l]bang ([r]? (rght b))) * ([l]? (lft b)).

rules structural.

% Contraction left
(not (lft a)) * ([l]? (lft a)) | ([l]? (lft a)).
(not (lft b)) * ([l]? (lft b)) | ([l]? (lft b)).

% Weakening left
(not (lft a)) * bot.
(not (lft b)) * bot.

