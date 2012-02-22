%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for LJQ*              %
%                                           %
% Giselle Machado Reis - 2012               %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l unb.
subexp r unb.
subexp f lin.

subexprel r < l.

% Init
(not (lft A)) , (not (rght A)).

% Bottom
(not (lft bottom)).

% Implication
lft (imp A B) := ([l]bang ([f]? (rght A))) , ([r]bang ([l]? (lft B))).
rght (imp A B) := [l]bang (([l]? (lft A)) | ([r]? (rght B))).

% Disjunction
lft (or A B) := ([r]bang ([l]? (lft A))) , ([r]bang ([l]? (lft B))).
rght (or A B) := [r]bang (([r]? (rght A)) | ([r]? (rght B))).

% Conjunction
lft (and A B) := [r]bang (([l]? (lft A)) | ([l]? (lft B))).
rght (and A B) := ([r]bang ([f]? (rght A))) , ([r]bang ([f]? (rght B))).

