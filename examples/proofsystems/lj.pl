subexp l unb. % holds formulas of the left-hand side of the sequent
subexp r lin. % holds formulas of the right-hand side of the sequent

%% Specification of Intuitionistic Logic

rght (iand a b) :: ([r]? (rght a)) & ([r]? (rght b)).
lft (iand c d) :: ([l]? (lft c)) | ([l]? (lft d)).
rght (ior f g) :: ([r]? (rght f)) ; ([r]? (rght g)).
lft (ior h i) :: ([l]? (lft h)) & ([l]? (lft i)).
rght (iimp j k) :: ([l]? (lft j)) | ([r]? (rght k)).
lft (iimp m n) :: ([l]bang ([r]? (rght m))) , ([l]? (lft n)).

