%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for LL                %
%                                           %
% Elaine Pimentel   -   2012                %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp lr lin.

subexpctx lr many rghtlft.

rules introduction.

% Implication
(not (lft (lolli A B))) * (([lr]? (rght A)) * ([lr]? (lft B))).
(not (rght (lolli A B))) *  (([lr]? (lft A)) | ([lr]? (rght B))).

% Tensor
(not (lft (tensor A B))) * (([lr]? (lft A)) | ([lr]? (lft B))).
(not (rght (tensor A B))) * (([lr]? (rght A)) * ([lr]? (rght B))).

% With
(not (lft (with A B))) * (([lr]? (lft A)) + ([lr]? (lft B))).
(not (rght (with A B))) * (([lr]? (rght A)) & ([lr]? (rght B))).

% Par
(not (lft (par A B))) * (([lr]? (lft A)) * ([lr]? (lft B))).
(not (rght (par A B))) * (([lr]? (rght A)) | ([lr]? (rght B))).

% Oplus
(not (lft (oplus A B))) * (([lr]? (lft A)) & ([lr]? (lft B))).
(not (rght (oplus A B))) * (([lr]? (rght A)) + ([lr]? (rght B))).

% Bang
(not (lft (lbang A))) * (? (lft A)).
(not (rght (lbang A))) * (bang (rght A)).

% Quest
(not (lft (lquest A))) * (bang (lft A)).
(not (rght (lquest A))) * (? (rght A)).

% One
(not (lft lone)) * bot.
(not (rght lone)) * one.

% Bottom
(not (lft lbot)) * one.
(not (rght lbot)) * bot.

% Zero
(not (lft lzero)) * top.

% Top
(not (rght ltop)) * top.

rules axiom.
((not (lft A)) * (not (rght A))).

rules cut.
(([lr]? (rght A)) * ([lr]? (lft A))).



