(*****************************************)
(*                                       *)
(*  All the code related to calling DLV  *)
(*                                       *)
(*  Giselle Machado Reis                 *)
(*  2013                                 *)
(*                                       *)
(*****************************************)

open Sequent

(* Definitions for the dlv file *)

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

(* removed definition *)
let removed_clauses_set =
"% removed(F, G, G1): removing the formula F from context G yields the context G1\n
in(F1, G1) :- removed(F, G, G1), in(F1, G), F != F1.\n\n"

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

(* Generating models for a set of constraints *)

(* Print constraints to a file *)
let rec printToFile cst out = 
  Printf.fprintf out "%s" (Constraints.toString cst)

(* Generates a file with the constraint set and the theory specification *)
let genFile cstrSet name = 
  let file = open_out ("solver/"^name^".in") in
  Printf.fprintf file "%s" description;
  Printf.fprintf file "%s" union_clauses_set;
  Printf.fprintf file "%s" elin_clauses_set;
  Printf.fprintf file "%s" emp_clauses_set;
  Printf.fprintf file "%s" mctx_clauses_set;
  Printf.fprintf file "%s" addform_clauses_set;
  Printf.fprintf file "%s" removed_clauses_set;
  Printf.fprintf file "%s" aux_clauses_set;
  printToFile cstrSet file;
  close_out file

(* Get the models from one set of constraints *)
(* This function will return a list of models. These models are represented
as strings which are the true predicated in the format of facts (e.g.
"pred(a). pred(b)." *)
let getModels cstrSet = 
  genFile cstrSet "temp";
  (*let sedStr = " | sed \"s/{//\" | sed \"s/}/./\" | sed \"s/[a-zA-Z]*\\(\\), /. /g\" " in
  let channel = Unix.open_process_in ("dlv -silent solver/temp.in"^sedStr) in*)
  let channel = Unix.open_process_in ("dlv -silent solver/temp.in") in
  let rec readModel input = try match input_line input with
    | str -> 
      let lexbuf = Lexing.from_string str in
      let model = Parser_models.model Lexer_models.token lexbuf in
      (Constraints.create model) :: readModel input
    with End_of_file -> let _ = Unix.close_process_in channel in []
  in
  readModel channel

(* Deciding the permutation condition *)

let ctxPredicates lvsLst treeName = 
  let ctxForLeaf leaf leafIdx treeName = 
    let ctx = SequentSchema.getContext leaf in
    List.fold_right ( fun (subexp, index) acc ->
      let ctxName = ContextSchema.ctxToStr (subexp, index) in
      let subexpName = Prints.remSpecial subexp in
      let subexpType = Subexponentials.typeAsString subexp in
      let leafName = treeName ^ "_leaf" ^ (string_of_int leafIdx) in
      ("ctx(" ^ ctxName ^ ", " ^ subexpName ^ ", " ^ subexpType ^ ", " ^ leafName ^ ", " ^ treeName ^ ").\n") ^ acc 
    ) (ContextSchema.getContexts ctx) ""
  in
  let i = ref 0 in
  List.fold_right (fun leaf acc ->
    i := !i + 1;
    (ctxForLeaf leaf !i treeName) ^ acc
  ) lvsLst ""

(* Decides whether a proof of der1 implies in a proof of der2 *)
let proofImplies (der1, model1) (der2, model2) =
  let openLeaves1 = ProofTreeSchema.getOpenLeaves der1 in
  let openLeaves2 = ProofTreeSchema.getOpenLeaves der2 in
  let str1 = ctxPredicates openLeaves1 "tree1" in
  let str2 = ctxPredicates openLeaves2 "tree2" in
  (* TODO: finish! Add also the models to the input file. *)
  true

let subexpOrdStr () = Hashtbl.fold (fun key data acc ->
  "geq("^(Prints.remSpecial data)^", "^(Prints.remSpecial key)^").\n"^acc
) Subexponentials.orderTbl ""
let reflSubexpRel () = Hashtbl.fold (fun key data acc -> 
  "geq("^(Prints.remSpecial key)^", "^(Prints.remSpecial key)^").\n"^acc
) Subexponentials.typeTbl ""

let genPermFile cList ctxStr okStr model name =  
  let file = open_out ("solver/"^name^".in") in
  Printf.fprintf file "%s" description;
  Printf.fprintf file "%s" union_clauses_set;
  Printf.fprintf file "%s" elin_clauses_set;
  Printf.fprintf file "%s" emp_clauses_set;
  Printf.fprintf file "%s" mctx_clauses_set;
  Printf.fprintf file "%s" addform_clauses_set;
  Printf.fprintf file "%s" removed_clauses_set;
  Printf.fprintf file "%s" aux_clauses_set;
  Printf.fprintf file "%s" proveIf_clauses;
  Printf.fprintf file "%s\n" okStr;
  Printf.fprintf file "%s" (reflSubexpRel ());
  Printf.fprintf file "%s" (subexpOrdStr ());
  Printf.fprintf file "%s" ctxStr;
  Printf.fprintf file "%s\n" model;
  printToFile cList file;
  close_out file

(* Checks if some set of constraints and the model m satisfy the
permutability condition *)
(*
let permCondition cstrs ctxStr okStr mdl =
  let lst = cstrs.lst in
  let rec condition mdl cList = match cList with
    | [] -> false
    | c :: tl ->
      genPermFile c ctxStr okStr mdl ("temp_perm"^(string_of_int !i));
      let channel = Unix.open_process_in ("dlv -silent solver/temp_perm"^(string_of_int !i)^".in") in
      i := !i + 1;
      try match input_line channel with
        | _ -> let _ = Unix.close_process_in channel in 
          (*print_endline "Some model is satisfiable."; flush
          (out_channel_of_descr stdout)*) (); 
          true
        with End_of_file -> let _ = Unix.close_process_in channel in condition mdl tl
  in
  condition mdl lst
*)
