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
%% ![l] must require r to be empty.
not (lft (lolli A B)) * ![l] ?[r] (rght A) * ?[l] (lft B).
not (rght (lolli A B)) * ![l] (?[l] (lft A) | ?[r] (rght B)).

% Tensor
not (lft (tensor A B)) * ?[l] (lft A) | ?[l] (lft B).
not (rght (tensor A B)) * ![l] ?[r] (rght A) * ![l] ?[r] (rght B).

% With
not (lft (with A B)) * ?[l] (lft A) + ?[l] (lft B).
not (rght (with A B)) * ![l] (?[r] (rght A) & ?[r] (rght B)).

% Oplus
not (lft (oplus A B)) * ?[l] (lft A) & ?[l] (lft B).
not (rght (oplus A B)) * ![l] ?[r] (rght A) + ![l] ?[r] (rght B).

% Bang
not (lft (lbang A)) * ?[l] (lft A).
not (rght (lbang A)) * ![lb] ?[r] (rght A).

% One
not (lft lone) * bot.
not (rght lone) * one.

% Zero
not (lft lzero) * top.

% Top
not (rght ltop) * ![l] top.

rules axiom.
not (lft A) * not (rght A).

rules cut.
![l] ?[r] (rght A) * ?[l] (lft A).


