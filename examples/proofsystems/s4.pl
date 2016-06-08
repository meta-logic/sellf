%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for S4 (modal logic)  %
%                                           %
% Giselle Reis - 2012                       %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l  unb.
subexp r  unb.
subexp nl unb. % Necessarily left
subexp pr unb. % Possibly right

subexpctx l many ant.
subexpctx r many suc.
subexpctx nl many ant [nec].
subexpctx pr many suc [poss].

subexprel pr < nl.

rules introduction.
% Conjunction
(not (lft (and A B))) * ([l]? (lft A)) | ([l]? (lft B)).
(not (rght (and A B))) * (([r]? (rght A)) * ([r]? (rght B))).

% Implication
(not (lft (imp A B))) * (([r]? (rght A)) * ([l]? (lft B))).
(not (rght (imp A B))) * ([l]? (lft A)) | ([r]? (rght B)).

% Necessarily
(not (lft (nec A))) * [l]? (lft A).
(not (rght (nec A))) * [pr]bang ([r]? (rght A)).

% Possibly
(not (lft (poss A))) * [pr]bang ([l]? (lft A)).
(not (rght (poss A))) * [r]? (rght A).

rules axiom.
% Init
((not (lft A)) * (not (rght A))).

rules cut.
% Cut
(([l]? (lft A)) * ([r]? (rght A))).

%rules structural.
% Structural rules for modals
%((not (lft (nec A))) * ([nl]? (lft (nec A)))).
%((not (rght (poss A))) * ([pr]? (rght (poss A)))).

