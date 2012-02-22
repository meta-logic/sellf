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

subexprel r < pr.
subexprel l < nl.
subexprel e < pr.
subexprel e < nl.

% Conjunction
lft (and A B) := ([l]? (lft A)) | ([l]? (lft B)).
rght (and A B) := ([r]? (rght A)) , ([r]? (rght B)).

% Implication
lft (imp A B) := ([r]? (rght A)) , ([l]? (lft B)).
rght (imp A B) := ([l]? (lft A)) | ([r]? (rght B)).

% Necessarily
lft (nec A) := [l]? (lft A).
rght (nec A) := [e]bang ([r]? (rght A)).

% Possibly
lft (poss A) := [e]bang ([l]? (lft A)).
rght (poss A) := [r]? (rght A).

% Init
(not (lft A)) , (not (rght A)).

% Cut
([l]? (lft A)) , ([r]? (rght A)).

% Structural rules for modals
(not (lft (poss A))) , ([nl]? (lft (poss A))).
(not (rght (nec A))) , ([pr]? (rght (nec A))).

