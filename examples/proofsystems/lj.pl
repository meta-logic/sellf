%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for LJ                %
%                                           %
% Giselle Machado Reis - 2011               %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% THIS IS NOT CORRECT NOR COMPLETE

subexp l unb. % holds formulas of the left-hand side of the sequent
subexp r lin. % holds formulas of the right-hand side of the sequent

% Implication
lft (imp A B) := ([l]bang ([r]? (rght mA))) , ([l]? (lft B)).
rght (imp A B) := ([l]? (lft A)) | ([r]? (rght B)).

% Conjunction
lft (and A B) := ([l]? (lft A)) ; ([l]? (lft B)).
rght (and A B) := ([r]? (rght A)) & ([r]? (rght B)).

% Disjunction
lft (or A B) := ([l]? (lft A)) & ([l]? (lft B)).
rght (or A B) := ([r]? (rght A)) ; ([r]? (rght B)).


