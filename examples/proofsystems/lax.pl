%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for Lax Logic         %
%                                           %
% Giselle Machado Reis - 2012               %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l  unb.
subexp r  lin.
subexp cr lin.

subexprel r < cr.
subexprel cr < l.

% Conjunction
lft (and A B) := ([l]? (lft A)) | ([l]? (lft B)).
rght (and A B) := ([l]bang ([r]? (rght A))) , ([l]bang ([r]? (rght B))).

% Disjunction
lft (or A B) := ([l]? (lft A)) & ([l]? (lft B)).
rght (or A B) := ([l]bang ([r]? (rght A))) ; ([l]bang ([r]? (rght B))).

% Implication
lft (imp A B) := ([r]? (rght A)) , ([l]? (lft B)).
rght (imp A B) := [l]bang (([l]? (lft A)) | ([r]? (rght B))).

% Circ
lft (circ A) := [cr]bang ([l]? (lft A)).
rght (circ A) := [l]bang ([r]? (rght A)).

% Initial
(not (lft A)) , (not (rght A)).

% Cut
([l]? (lft A)) , ([l]bang ([r]? (rght A))).

% Structural rule for circ
(not (rght (circ A))) , ([cr]? (rght (circ A))).

