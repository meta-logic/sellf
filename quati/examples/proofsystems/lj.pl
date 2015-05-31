%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                             %
% SELLF specification for LJ  %
%                             %
% Elaine Pimentel - 2012      %
%                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp r lin.
subexp l unb.

subexpctx r single rght.
subexpctx l many lft.

rules introduction.

% Implication
(not (lft (imp A B))) *  (([l]bang ([r]? (rght A))) * ([l]? (lft B))).
(not (rght (imp A B))) *  (([l]? (lft A)) | ([r]? (rght B))).

% Conjunction
(not (lft (and A B))) * (([l]? (lft A)) + ([l]? (lft B))).
(not (rght (and A B))) * (([r]? (rght A)) & ([r]? (rght B))).

% Disjunction
(not (lft (or A B))) * (([l]? (lft A)) & ([l]? (lft B))).
(not (rght (or A B))) * (([r]? (rght A)) + ([r]? (rght B))).

% False
(not (lft false)) * top.

% True
(not (rght true)) * top.

rules axiom.
((not (lft A)) * (not (rght A))).

rules cut.
(([r]? (rght A)) * ([l]? (lft A))).
