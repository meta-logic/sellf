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
  
    val description : string
    val union_clauses_set : string
    val elin_clauses_set : string
    val emp_clauses_set : string
    val aux_clauses_set : string
    val proveIf_clauses : string
    val genFile : Constraints.constraintset -> string -> unit
    val getModels : Constraints.constraintset -> Constraints.constraintset list
    val ctxPredicates : SequentSchema.sequent list -> string -> string
    (* TODO: Remove the polymorphic type *)
    val okIfProve : 'a list -> string -> string
    val subexpOrdStr : unit -> string
    val reflSubexpRel : unit -> string
    val genPermutationFile : string -> string -> string -> string -> string -> string -> unit
    val proofImplies : ProofTreeSchema.prooftree * Constraints.constraintset -> ProofTreeSchema.prooftree * Constraints.constraintset -> bool
  
  end

module Dlv : DLV = struct

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

  % If all the leaves of the second tree are not provable, no models are generated
  :- not ok.\n\n"

  (* Generating models for a set of constraints *)

  (* Generates a file with the constraint set and the theory specification *)
  let genFile cstrSet name = 
    let file = open_out ("solver/"^name^".in") in
    Printf.fprintf file "%s" description;
    Printf.fprintf file "%s" union_clauses_set;
    Printf.fprintf file "%s" elin_clauses_set;
    Printf.fprintf file "%s" emp_clauses_set;
    Printf.fprintf file "%s" aux_clauses_set;
    Printf.fprintf file "%s" (Constraints.toString cstrSet);
    close_out file

  (* Get the models from one set of constraints *)
  (* This function will return a list of models. These models are represented
  as strings which are the true predicated in the format of facts (e.g.
  "pred(a). pred(b)." *)
  let getModels cstrSet =
    genFile cstrSet "temp";
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

  (* Generates the string "ok :- \forall l \in leafs. proveIf(lname, _)." *)
  let okIfProve leafs treeName = 
    let i = ref 0 in
    let rec okIfProve_aux leafs = match leafs with
      | [] -> ""
      | [_] ->
	i := !i + 1;
	let leafName = treeName ^ "_leaf" ^ (string_of_int !i) in
	"provIf(" ^ leafName ^ ", _)."
      | _ :: tl -> 
	i := !i + 1;
	let leafName = treeName ^ "_leaf" ^ (string_of_int !i) in
	"provIf(" ^ leafName ^ ", _), " ^ (okIfProve_aux tl)
    in
    "ok :- " ^ (okIfProve_aux leafs)

  let subexpOrdStr () = Hashtbl.fold (fun key data acc ->
    "geq("^(Prints.remSpecial data)^", "^(Prints.remSpecial key)^").\n"^acc
  ) Subexponentials.orderTbl ""
  let reflSubexpRel () = Hashtbl.fold (fun key data acc -> 
    "geq("^(Prints.remSpecial key)^", "^(Prints.remSpecial key)^").\n"^acc
  ) Subexponentials.typeTbl ""

  let genPermutationFile ctxStr1 ctxStr2 modelStr1 modelStr2 okStr name =  
    let file = open_out (name) in
    Printf.fprintf file "%s" description;
    Printf.fprintf file "%s" union_clauses_set;
    Printf.fprintf file "%s" elin_clauses_set;
    Printf.fprintf file "%s" emp_clauses_set;
    Printf.fprintf file "%s" aux_clauses_set;
    Printf.fprintf file "%s" proveIf_clauses;
    Printf.fprintf file "%s" (reflSubexpRel ());
    Printf.fprintf file "%s" (subexpOrdStr ());
    Printf.fprintf file "%s\n" modelStr1;
    Printf.fprintf file "%s\n" modelStr2;
    Printf.fprintf file "%s\n" ctxStr1;
    Printf.fprintf file "%s\n" ctxStr2;
    Printf.fprintf file "%s\n" okStr;
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
    let fileName = "solver/permute.in" in
    genPermutationFile ctxStr1 ctxStr2 modelStr1 modelStr2 okStr fileName;
    let channel = Unix.open_process_in ("dlv -silent " ^ fileName) in 
    let rec hasModel input = try match input_line input with
      | _ -> let _ = Unix.close_process_in channel in true (* If some line is printed, it means that there is a model *)
      with End_of_file -> let _ = Unix.close_process_in channel in false
    in
    hasModel channel  

end;;
