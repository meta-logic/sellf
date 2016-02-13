(*****************************************)
(*                                       *)
(*  All the code related to calling DLV  *)
(*                                       *)
(*  Giselle Machado Reis                 *)
(*  2013                                 *)
(*                                       *)
(*****************************************)

open ContextSchema
open Sequent
open ProofTreeSchema

module type DLV = 
  sig
  
    val header_title : string
    val header_multiset_spec : string
    val header_proveIf_spec : string
    val title_multiset : string
    val multiset_clauses : string
    val title_proveIf : string
    val proveIf_clauses : string
    val title_facts : string
    val genFile : Constraints.constraintset -> string -> unit
    val getModels : Constraints.constraintset -> Constraints.constraintset list
    val ctxPredicates : SequentSchema.sequent list -> string -> string
    val okIfProve : SequentSchema.sequent list -> string -> string
    val subexpOrdStr : unit -> string
    val reflSubexpRel : unit -> string
    val genPermutationFile : string -> string -> string -> string -> string -> string -> unit
    val proofImplies : ProofTreeSchema.prooftree * Constraints.constraintset -> ProofTreeSchema.prooftree * Constraints.constraintset -> bool
  
  end

module Dlv : DLV = struct

  (* Definitions for the dlv file *)
  (* The indentation is strange but necessary for a well-formatted output file *)

  let header_title = "
% Predicate specification:
%"

  let header_multiset_spec = "
%
% in(F, Ctx, N) -> Formula F occurs in Ctx N times
% in_unique(F, I, C) -> Represents one occurrence of F in C
% union(C1, C2, C) -> C = C1 U C2
% minus(C1, F, C0) -> C0 = C1 - F
% emp(C) -> C is the empty set
%"

  let header_proveIf_spec = "
% proveIf(S2, S1) -> Sequent S2 is provable if sequent S1 is provable.
% not_proveIf(S2, S1) -> Sequent S2 cannot be proven from a proof of sequent S1
% ctx(C, SE, lin/unb, Seq, Tree) -> The context C represents subexponential SE
%       which is lin/unb in sequent Seq and proof tree Tree.
% in_sequent_tree{1,2}(F, SE, lin/unb, S, N) -> Formula F occurs in 
%       subexponential SE, which is lin/unb, N times in sequent S and
%       proof tree {1,2}.
%
"

  let title_multiset = "
%%%%%%%%%%%%%%%% Clauses for multi-set operations in contexts %%%%%%%%%%%%%%%%%
"

  let multiset_clauses = "
% Considering that there are not more than 5 copies of the same formula
#maxint=5.

% Distinguishes formula occurrences
in_unique(F, I, C) :- in(F, C, N), #int(I), 1 <= I, I <= N.

% Distributes each copy individually
in_unique(F, I, C1) v in_unique(F, I, C2) :- in_unique(F, I, C), union(C1, C2, C).
% Avoids duplicated results
:- in_unique(F, I, C), in_unique(F, I1, C1), in_unique(F, I2, C2), I1 > I2, union(C1, C2, C).

% C0 = C1 - {F}
% Every formula occurring in C0 is also in C1
in_unique(F, I, C1) :- minus(C1, _, C0), in_unique(F, I, C0).
% C1 has one extra occurrence of F
contained(F, C) :- max_index(F, _, C).
% Index 1 if it's the first occurrence
in_unique(F, 1, C1) :- minus(C1, F, C0), not contained(F, C0).
% Otherwise index max_index + 1
not_max_index(F, I, C) :- in_unique(F, I, C), in_unique(F, J, C), J > I.
max_index(F, I, C) :- in_unique(F, I, C), not not_max_index(F, I, C).
in_unique(F, I, C1) :- minus(C1, F, C0), contained(F, C0), max_index(F, J, C0), I = J+1.

:- in_unique(F, I, C), I > 0, emp(C).

emp(C1) :- emp(C), union(C1, C2, C).
emp(C2) :- emp(C), union(C1, C2, C).
emp(C) :- emp(C1), emp(C2), union(C1, C2, C).

% count the copies of elements in all sets and translate back to original notation
in_final(F, C, Count) :- in_unique(F, _, C), Count = #count{ I : in_unique(F, I, C) }, #int(Count).
"

  let title_proveIf = "
%%%%%%%%%%%%%%%  Clauses to certify: proof of S1 => proof of S2 %%%%%%%%%%%%%%%%
"

  let proveIf_clauses = "
proveIf(S2, S1) :- 
  not not_proveIf(S2, S1), 
  ctx(_, _, _, S2, tree2), 
  ctx(_, _, _, S1, tree1).

in_sequent_tree1(F, SE, TP, S, M) :- in(F, C, M), M > 0, ctx(C, SE, TP, S, tree1).
in_sequent_tree2(F, SE, TP, S, M) :- in(F, C, M), M > 0, ctx(C, SE, TP, S, tree2).
in_sequent_tree2_simple(F, S2) :- in(F, C, M), M > 0, ctx(C, SE, TP, S2, tree2).

% S2 must be provable from a proof of S1.
% Here we specify the cases where this does not happen.

% For unbounded and bounded subexponentials:
% 1. S1 has a formula that is not in S2 at all or
% 2. S1 has a formula that is in S2 but in a lower subexponential
%    (remember that formulas can always be downgraded, but never upgraded).

% Additionally, for bound subexponentials:
% 3. S1 has a formula F n times and S2 has the same formula m times and n != m 
%    (considering that the occurrences must be in the same subexponential)

% 1. S1 has a formula that is not in S2
not_proveIf(S2, S1) :- 
  in_sequent_tree1(F, _, _, S1, _),
  % This might seem redundant but is necessary to make the rule safe.
  not in_sequent_tree2_simple(F, S2), ctx(C, _, _, S2, tree2).
  % Represets the unsafe literal:
  % not in_sequent_tree2(F, _, _, S2, _).
  
% 2. S1 has a formula that is in S2 but in a lower subexponential
not_proveIf(S2, S1) :- 
  in_sequent_tree1(F, SE1, _, S1, _),
  in_sequent_tree2(F, SE2, _, S2, _),
  not geq(SE2, SE1).

% 3. S1 and S2 both have a formula in a linear subexponential 
%    but with different multiplicity
not_proveIf(S2, S1) :- 
  in_sequent_tree1(F, SE, lin, S1, M),
  in_sequent_tree2(F, SE, lin, S2, N),
  M != N.

% If not all the leaves of the second tree are provable, no models are generated
:- not ok.
"

  let title_facts = "
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Facts %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
"

  (* Generating models for a set of constraints *)

  (* Generates a file with the constraint set and the theory specification *)
  let genFile cstrSet name = 
    let file = open_out ("solver/"^name^".in") in
    Printf.fprintf file "%s" header_title;
    Printf.fprintf file "%s" header_multiset_spec;
    Printf.fprintf file "%s" title_multiset;
    Printf.fprintf file "%s" multiset_clauses;
    Printf.fprintf file "%s" title_facts;
    Printf.fprintf file "%s" (Constraints.toString cstrSet);
    close_out file

  (* Get the models from one set of constraints *)
  (* This function will return a list of models. These models are represented
  as strings which are the true predicated in the format of facts (e.g.
  "pred(a). pred(b)." *)
  let getModels cstrSet =
    genFile cstrSet "temp2";
    let channel = Unix.open_process_in ("dlv -silent solver/temp2.in") in
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
	let subexpType = Subexponentials.typeAsString subexp in
	let leafName = treeName ^ "_leaf" ^ (string_of_int leafIdx) in
	("ctx(" ^ ctxName ^ ", " ^ subexp ^ ", " ^ subexpType ^ ", " ^ leafName ^ ", " ^ treeName ^ ").\n") ^ acc 
      ) (ContextSchema.getContexts ctx) ""
    in
    let i = ref 0 in
    List.fold_right (fun leaf acc ->
      i := !i + 1;
      (ctxForLeaf leaf !i treeName) ^ acc
    ) lvsLst ""

  (* Generates the string "ok :- \forall l \in leafs. proveIf(lname, _)." *)
  let okIfProve leafs treeName = 
    let i = ref 0 in
    let rec okIfProve_aux leafs = match leafs with
      | [] -> ""
      | [_] ->
	i := !i + 1;
	let leafName = treeName ^ "_leaf" ^ (string_of_int !i) in
	"proveIf(" ^ leafName ^ ", _)."
      | _ :: tl -> 
	i := !i + 1;
	let leafName = treeName ^ "_leaf" ^ (string_of_int !i) in
	"proveIf(" ^ leafName ^ ", _), " ^ (okIfProve_aux tl)
    in
    "ok :- " ^ (okIfProve_aux leafs)

  let subexpOrdStr () = Hashtbl.fold (fun key data acc ->
    "geq("^data^", "^key^").\n"^acc
  ) Subexponentials.orderTbl ""
  let reflSubexpRel () = Hashtbl.fold (fun key data acc -> 
    "geq("^key^", "^key^").\n"^acc
  ) Subexponentials.typeTbl ""

  let genPermutationFile ctxStr1 ctxStr2 modelStr1 modelStr2 okStr name =  
    let file = open_out (name) in
    Printf.fprintf file "%s" header_title;
    Printf.fprintf file "%s" header_multiset_spec;
    Printf.fprintf file "%s" header_proveIf_spec;
    Printf.fprintf file "%s" title_multiset;
    Printf.fprintf file "%s" multiset_clauses;
    Printf.fprintf file "%s" title_proveIf;
    Printf.fprintf file "%s" proveIf_clauses;
    Printf.fprintf file "%s\n" okStr;
    Printf.fprintf file "%s" title_facts;
    Printf.fprintf file "%s" (reflSubexpRel ());
    Printf.fprintf file "%s" (subexpOrdStr ());
    Printf.fprintf file "%s\n" modelStr1;
    Printf.fprintf file "%s\n" modelStr2;
    Printf.fprintf file "%s\n" ctxStr1;
    Printf.fprintf file "%s\n" ctxStr2;
    close_out file

  (* Decides whether a proof of der1 implies in a proof of der2 *)
  let proofImplies (der1, model1) (der2, model2) =
    let openLeaves1 = ProofTreeSchema.getOpenLeaves der1 in
    let openLeaves2 = ProofTreeSchema.getOpenLeaves der2 in
    let ctxStr1 = ctxPredicates openLeaves1 "tree1" in
    let ctxStr2 = ctxPredicates openLeaves2 "tree2" in
    let modelStr1 = Constraints.toString model1 in
    let modelStr2 = Constraints.toString model2 in
    let okStr = okIfProve openLeaves2 "tree2" in
    let fileName = "solver/permute2.in" in
    genPermutationFile ctxStr1 ctxStr2 modelStr1 modelStr2 okStr fileName;
    let channel = Unix.open_process_in ("dlv -silent " ^ fileName) in 
    let rec hasModel input = try match input_line input with
      | _ -> let _ = Unix.close_process_in channel in true (* If some line is printed, it means that there is a model *)
      with End_of_file -> let _ = Unix.close_process_in channel in false
    in
    hasModel channel  

end;;
