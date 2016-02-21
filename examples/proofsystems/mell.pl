%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for ILL               %
%                                           %
% Giselle Reis  -   2016                    %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l lin.
subexp lb lin. % Formulas with ! on the left.
subexp r lin.

subexpctx l many ant.
subexpctx lb many ant [lbang].
subexpctx r single suc.

subexprel l < lb.

rules introduction.

% Implication
%% [l]bang must require r to be empty.
(not (lft (lolli A B))) * (([l]bang ([r]? (rght A))) * ([l]? (lft B))).
(not (rght (lolli A B))) *  (([l]? (lft A)) | ([r]? (rght B))).

% Tensor
(not (lft (tensor A B))) * (([l]? (lft A)) | ([l]? (lft B))).
(not (rght (tensor A B))) * (([r]? (rght A)) * ([r]? (rght B))).

% Bang
(not (lft (lbang A))) * ([l]? (lft A)).
(not (rght (lbang A))) * ([lb]bang ([r]? (rght A))).

% One
(not (lft lone)) * bot.
(not (rght lone)) * one.

rules axiom.
((not (lft A)) * (not (rght A))).

rules cut.
(([r]? (rght A)) * ([l]? (lft A))).


