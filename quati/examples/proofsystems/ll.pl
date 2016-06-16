%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for LL                %
%                                           %
% Elaine Pimentel   -   2012                %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l lin.
subexp r lin.
subexp bl unb. % banged formulas on the left (represented with a star)
subexp qr unb. % question marked formulas on the right (represented with a heart)

subexpctx l many ant.
subexpctx r many suc.
subexpctx bl many ant [lbang].
subexpctx qr many suc [lquest].

subexprel bl < qr.

rules introduction.

% Implication
(not (lft (lolli A B))) * (([r]? (rght A)) * ([l]? (lft B))).
(not (rght (lolli A B))) *  (([l]? (lft A)) | ([r]? (rght B))).

% Tensor
(not (lft (tensor A B))) * (([l]? (lft A)) | ([l]? (lft B))).
(not (rght (tensor A B))) * (([r]? (rght A)) * ([r]? (rght B))).

% With
(not (lft (with A B))) * (([l]? (lft A)) + ([l]? (lft B))).
(not (rght (with A B))) * (([r]? (rght A)) & ([r]? (rght B))).

% Par
(not (lft (par A B))) * (([l]? (lft A)) * ([l]? (lft B))).
(not (rght (par A B))) * (([r]? (rght A)) | ([r]? (rght B))).

% Oplus
(not (lft (oplus A B))) * (([l]? (lft A)) & ([l]? (lft B))).
(not (rght (oplus A B))) * (([r]? (rght A)) + ([r]? (rght B))).

% Bang
(not (lft (lbang A))) * ([l]? (lft A)).
(not (rght (lbang A))) * ([bl]bang ([r]? (rght A))).

% Quest
(not (lft (lquest A))) * ([bl]bang ([l]? (lft A))).
(not (rght (lquest A))) * ([r]? (rght A)).

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
(([r]? (rght A)) * ([l]? (lft A))).



