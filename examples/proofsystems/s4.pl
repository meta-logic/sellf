%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for S4 (modal logic)  %
%                                           %
% Giselle Machado Reis - 2012               %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l  unb.
subexp r  unb.
subexp nl unb. % Necessarily left
subexp pr unb. % Possibly right
subexp e  unb.

subexpctx l many lft.
subexpctx r many rght.
subexpctx nl many lft [nec].
subexpctx pr many rght [poss].

subexprel r < pr.
subexprel l < nl.
subexprel e < pr.
subexprel e < nl.

rules introduction.
% Conjunction
(not (lft (and A B))) * ([l]? (lft A)) | ([l]? (lft B)).
(not (rght (and A B))) * (([r]? (rght A)) * ([r]? (rght B))).

% Implication
(not (lft (imp A B))) * (([r]? (rght A)) * ([l]? (lft B))).
(not (rght (imp A B))) * ([l]? (lft A)) | ([r]? (rght B)).

% Necessarily
(not (lft (nec A))) * [l]? (lft A).
(not (rght (nec A))) * [e]bang ([r]? (rght A)).

% Possibly
(not (lft (poss A))) * [e]bang ([l]? (lft A)).
(not (rght (poss A))) * [r]? (rght A).

rules axiom.
% Init
((not (lft A)) * (not (rght A))).

rules cut.
% Cut
(([l]? (lft A)) * ([r]? (rght A))).

rules structural.
% Structural rules for modals
((not (lft (nec A))) * ([nl]? (lft (nec A)))).
((not (rght (poss A))) * ([pr]? (rght (poss A)))).

