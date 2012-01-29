subexp defs unb.
subexp l unb.
subexp r unb.
subexp rr unb.

subexprel l <= defs.
subexprel r <= defs.
subexprel rr <= defs.
subexprel r <= rr.
subexprel rr <= l.

context defs.

% Not possible because there's no way to put the cut rule in the context.

%lft (bottom).

% Init and cut rules are not part of the specification

%lft (A) :- rght (A).
% I think this question mark is not allowed on the left-hand side. Returns
% syntax error.
%[l]? lft (A) :- [r]? rght (A).

%% In Elaine's specification, & is substituted with oplus (;)

lft (imp A B) :- ([r]? (rght A)) & ([l]? (lft B)).
rght (imp A B) :- [l]bang ( ([l]? (lft A)) | ([r]? (rght B))).

lft (and A B) :- ([l]? (lft A)) | ([l]? (lft B)).
rght (and A B) :- ([r]? (rght A)) & ([r]? (rght B)).

lft (or A B) :- ([l]? (lft A)) & ([l]? (lft B)).
rght (or A B) :- ([r]? (rght A)) | ([r]? (rght B)).

% Think about how to define quantifiers.
%lft (forall A) :- [l]? (pi X\ (lft (A X))).
%rght (forall A) :- [l]bang (pi x\ ([r]? (rght A x))).

%lft (exists A) :- pi x\ ([l]? (lft A x)).
%rght (exists A) :- [r]? (rght B X).

