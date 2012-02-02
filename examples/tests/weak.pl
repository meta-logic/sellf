subexp l unb. % holds formulas of the left-hand side of the sequent
subexp r unb. % holds formulas of the right-hand side of the sequent

%% Specification of two rules that require weakening to be permutable

% Takes a formula from the lhs and puts it on the rhs
lft (r1 a) :: ([r]? (rght a)).
% Erases all the formulas of the rhs
rght (r2 b) :: [l]bang ([r]? (rght b)).

