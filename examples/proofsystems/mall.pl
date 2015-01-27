%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for MALL              %
%                                           %
% Giselle Reis   -   2015                   %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp lr lin.
subexp un unb.

subexpctx lr many rghtlft.
subexpctx un many rghtlft.

rules introduction.

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

rules axiom.
((not (lft A)) * (not (rght A))).


