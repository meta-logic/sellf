%subexp spec unb.
%subexp init unb.
subexp l unb.
subexp r unb.

%subexprel l <= init.
%subexprel r <= init.

%context init.

% Init and cut rules are not part of the specification

%Id1
%lft (A) , rght (A).
%Id2
%[l]? lft (A) , [r]? rght (A).

%context spec.

%lft (imp A B) :: ([r]? (rght A)) & ([l]? (lft B)).
%rght (imp A B) :: [l]bang ( ([l]? (lft A)) ; ([r]? (rght B))).

lft (and A B) :: ([l]? (lft A)) | ([l]? (lft B)).
%rght (and A B) :: ([r]? (rght A)) & ([r]? (rght B)).

%lft (or A B) :: ([l]? (lft A)) , ([l]? (lft B)).
rght (or A B) :: ([r]? (rght A)) | ([r]? (rght B)).

% Think about how to define quantifiers.
%lft (forall A) :: [l]? (pi X\ (lft (A X))).
%rght (forall A) :: [l]bang (pi x\ ([r]? (rght A x))).

%lft (exists A) :: pi x\ ([l]? (lft A x)).
%rght (exists A) :: [r]? (rght B X).

