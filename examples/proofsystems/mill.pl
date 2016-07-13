%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                               %
% SELLF specification for MILL                  %
% (Multiplicative intuitionistic linear logic)  %
%                                               %
% Giselle Reis  -   2016                        %
%                                               %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l lin.
subexp r lin.

subexpctx l many ant.
subexpctx r single suc.

rules introduction.

% Implication
%% ![l] must require r to be empty.
not (lft (lolli A B)) * ![l] ?[r] (rght A) * ?[l] (lft B).
not (rght (lolli A B)) *  ?[l] (lft A) | ?[r] (rght B).

% Tensor
not (lft (tensor A B)) * ?[l] (lft A) | ?[l] (lft B).
not (rght (tensor A B)) * ?[r] (rght A) * ?[r] (rght B).

% One
not (lft lone) * bot.
not (rght lone) * one.

rules axiom.
not (lft A) * not (rght A).

rules cut.
?[r] (rght A) * ?[l] (lft A).


