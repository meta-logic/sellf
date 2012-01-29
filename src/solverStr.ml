(* Definitions for the smodels file *)

let description = 
"% We use the following predicate names:
%
%  form(X) ->  Denotes that X is a formula;
%  in(X, Ctx) -> Denotes that the  formula X is in the context Ctx; 
%  union(C1, C2, C3)  -> Denotes that the union of the contexts C1 and C2
%    contains the same elements as the context C3;
% ctx(Ctx, Sub, Lin/Unb, Leaf, Tree) -> Denotes that the context Ctx belongs to the 
%   linear/unbounded subexponential of the open leaf Leaf of the tree Tree.
% in_geq(F, Sub, Leaf) -> Denotes that the formula F is in a context of a subexponential of 
%   of the Leaf that is greater than the subexponential Sub.
% provIf(Leaf1, Leaf2) -> Denotes that the Leaf1 is provable if Leaf2 is provable.\n\n"

(* union definition *)
let union_clauses_set =
"in(X, S) :- in(X, S1), union(S1, S2, S).
in(X, S) :- in(X, S2), union(S1, S2, S).
in(X, S1) v in(X, S2) :- in(X, S), union(S1, S2, S).\n\n"

(* elin definition *)
let elin_clauses_set = 
"in(F, G) :- elin(F, G).
:- in(F, G), elin(F1, G), F != F1.\n\n"

(* emp definition *)
let emp_clauses_set = 
":- in(X, G), emp(G).\n\n"

(* mctx definition *)
let mctx_clauses_set = 
"in(F, G) :- mctx(F, G).\n\n"

(* addform definition *)
let addform_clauses_set = 
"mctx(F, G1) :- addform(F, G, G1).
mctx(F1, G1) :- addform(F, G, G1), mctx(F1, G).\n\n"

(* for consistency *)
let aux_clauses_set = 
"emp(G1) :- emp(G), union(G1, G2, G).
emp(G2) :- emp(G), union(G1, G2, G).
elin(F, G1) v elin(F, G2) :- elin(F, G), union(G1, G2, G).
emp(G1) v emp(G2) :- elin(F, G), union(G1, G2, G).
emp(G) :- emp(G1), emp(G2), union(G1, G2, G).\n\n"

let proveIf_clauses = 
"
%% Clauses to certify: proof of Lf1 => proof of Lf2
provIf(Lf2, Lf1) :- not not_provIf(Lf2, Lf1), ctx(_, _, _, Lf2, tree2), ctx(_, _, _, Lf1, tree1).

% Every subexponential is greater than itself.
% TODO: not safe. Find a way to specify this.
% geq(X, X).

% Definition of in_leaf
in_leaf(F, Lf) :- in(F, C), ctx(C, _, _, Lf, _).

% There is a formula in S1 that is not present in S2
not_provIf(Lf2, Lf1) :- in(F, C1), ctx(C1, _, _, Lf1, tree1), not in_leaf(F, Lf2), ctx(_, _, _, Lf2, tree2).

% There is a formula in a linear context of S2 such that it is not in S1.
not_provIf(Lf2, Lf1) :- in(F, C2), ctx(C2, Sub2, lin, Lf2, tree2), not in_leaf(F, Lf1), ctx(_, _, _, Lf1, tree1).

% There is a formula in S1 that is in a lower context in S2.
not_provIf(Lf2, Lf1) :- in(F, C1), ctx(C1, Sub1, _, Lf1, tree1), in(F, C2), ctx(C2, Sub2, _, Lf2, tree2), not geq(Sub2, Sub1). 

% There is a formula in a linear context of S2 such that it is in S1 in a greater context.
%not_provIf(Lf2, Lf1) :- in(F, C2), ctx(C2, Sub2, lin, Lf2, tree2), in(F, C1), ctx(C1, Sub1, _, Lf1, tree1), not geq(Sub2, Sub1). 
"



