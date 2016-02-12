(**************************************)
(*                                    *)
(*      Derivation of a bipole        *)
(*                                    *)
(*  Giselle Machado Reis              *)
(*  2013                              *)
(*                                    *)
(**************************************)

open ContextSchema
open Dlv
open ProofTreeSchema
open Sequent
open Types

module type BIPOLE = 
  sig
    exception Not_bipole
    val toPairsProofModel : (ProofTreeSchema.prooftree * Constraints.constraintset list) list 
      -> (ProofTreeSchema.prooftree * Constraints.constraintset) list
    val deriveBipole : SequentSchema.sequent -> terms -> Constraints.constraintset list 
      -> (ProofTreeSchema.prooftree * Constraints.constraintset) list
    val bipole : terms -> (ProofTreeSchema.prooftree * Constraints.constraintset) list
    val get_bipoles : terms list -> (ProofTreeSchema.prooftree * Constraints.constraintset) list
  end

module Bipole : BIPOLE = struct
  
  (* Builds the possible bipoles from a formula in a sequent and a set of constraints *)
  (* Generates the necessary further constraints. *)
  (* Returns a list of pairs (proof tree * model) *)

  exception Not_bipole

  (* Transforms a list ((ProofTreeSchema * Constraints list) list) into a list of *)
  (* pairs consisting of a proof tree schema and a valid non-empty model *)
  let toPairsProofModel bipoles = List.fold_right (fun (pt, cstrlst) acc ->
    List.fold_right (fun cs acc ->
      let nonemptymodels = List.filter (fun m -> not (Constraints.isEmpty m)) (Dlv.getModels cs) in
      (List.map (fun model -> 
	(pt, model)) nonemptymodels) @ acc
    ) cstrlst acc
  ) bipoles []
  ;;

  let deriveBipole seq form constr = 

    (* Initialize the proof tree *)
    let pt0 = ProofTreeSchema.create seq in

    (* decide on the formula *)
    let (pt1, decidecstr) = ProofTreeSchema.decide pt0 form "infty" in

    (* Initial constraints *)
    let constraints : Constraints.constraintset list ref = ref constr in

    (* Resulting pairs of proofs and constraint sets *)
    let results : (ProofTreeSchema.prooftree * Constraints.constraintset list) list ref = ref [] in

    (* Builds the derivation of f as a bipole (one positive and one negative
    phase). *)
    let rec derive prooftree cont = 
      let conclusion = ProofTreeSchema.getConclusion prooftree in
      match (SequentSchema.getPhase conclusion, SequentSchema.getGoals conclusion) with

      | SYNC, [f] -> begin match Term.observe f with
	(* Release rule *)
	| WITH(_,_)
	| PARR(_,_)
	| TOP
	| BOT
	| FORALL(_,_,_)
	| QST(_)
	| PRED(_,_,NEG) 
	| NOT(PRED(_,_,POS)) ->
	  let (pt, c) = ProofTreeSchema.releaseDown prooftree in
	  constraints := List.map (fun cst -> Constraints.union cst c) !constraints;
	  derive pt cont

	| ADDOR(f1, f2) ->
	  let (pt1, c1) = ProofTreeSchema.applyAddOr1 prooftree f in
	  let currentconstraints = !constraints in
	  constraints := List.map (fun cst -> Constraints.union cst c1) !constraints;
	  derive pt1 (fun () ->
	    cont (); (* save the tree and constraints *)
	    constraints := currentconstraints;
	    let (pt2, c2) = ProofTreeSchema.applyAddOr2 prooftree f in
	    constraints := List.map (fun cst -> Constraints.union cst c1) !constraints;
	    derive pt2 cont
	  )

	| TENSOR(f1, f2) ->
	  let ((pt1, pt2), c) = ProofTreeSchema.applyTensor prooftree f in
	  constraints := List.map(fun cst -> Constraints.union cst c) !constraints;
	  derive pt1 (fun () -> derive pt2 cont)

	| EXISTS(s, i, f1) ->
	  let (pt, c) = ProofTreeSchema.applyExists prooftree f in
	  constraints := List.map(fun cst -> Constraints.union cst c) !constraints;
	  derive pt cont

	| ONE ->
	  let c = ProofTreeSchema.applyOne prooftree in
	  constraints := List.map (fun cst -> Constraints.union cst c) !constraints;
	  cont ()

	| BANG(s, f1) ->
	  let (pt, c) = ProofTreeSchema.applyBang prooftree f in
	  constraints := List.map (fun cst -> Constraints.union cst c) !constraints;
	  derive pt cont

	(* Initial rule *)
	| PRED(str, terms, POS) | NOT(PRED(str, terms, NEG)) ->
	  let c = ProofTreeSchema.applyInitial prooftree f in
	  constraints := Constraints.times !constraints c;
	  cont ()
	
	| _ -> failwith ("Invalid principal formula in synchronous phase: "^(Prints.termToString (Term.observe f)))

      end
      | ASYN, hd::tl -> begin match Term.observe hd with
	(* Release rule *)
	| ADDOR(_,_) 
	| TENSOR(_,_)
	| EXISTS(_,_,_)
	| ONE
	| BANG(_)
	| PRED(_,_,_)
	| NOT(PRED(_,_,_)) ->
	  let (pt, c) = ProofTreeSchema.releaseUp prooftree hd in
	  constraints := List.map(fun cst -> Constraints.union cst c) !constraints;
	  derive pt cont

	| WITH(f1, f2) ->
	  let ((pt1, pt2), c) = ProofTreeSchema.applyWith prooftree hd in
	  constraints := List.map(fun cst -> Constraints.union cst c) !constraints;
	  derive pt1 (fun () -> derive pt2 cont)

	| PARR(f1, f2) ->
	  let (pt, c) = ProofTreeSchema.applyParr prooftree hd in
	  constraints := List.map(fun cst -> Constraints.union cst c) !constraints;
	  derive pt cont

	| TOP -> ProofTreeSchema.applyTop prooftree; cont ()

	| BOT ->
	  let (pt, c) = ProofTreeSchema.applyBot prooftree hd in
	  constraints := List.map(fun cst -> Constraints.union cst c) !constraints;
	  derive pt cont
	
	| FORALL(s, i, f1) ->
	  let (pt, c) = ProofTreeSchema.applyForall prooftree hd in
	  constraints := List.map(fun cst -> Constraints.union cst c) !constraints;
	  derive pt cont

	| QST(subexp, f1) ->
	  let (pt, c) = ProofTreeSchema.applyQst prooftree hd in
	  constraints := List.map(fun cst -> Constraints.union cst c) !constraints;
	  derive pt cont

	| _ -> failwith ("Invalid principal formula in asynchronous phase: "^(Prints.termToString (Term.observe hd)))
	  
      end
      (* Do not decide for a second time. The end of this phase means the end of
      the bipole. *)
      | ASYN, [] -> cont ()
      | _ -> failwith "Invalid sequent while building a bipole derivation."

    in
    derive pt1 (fun () -> 
      (* Saves a copy of the proof and constraints *)
      results := (ProofTreeSchema.copy pt0, (List.map (fun c -> Constraints.copy c) !constraints)) :: !results;
    );
    toPairsProofModel !results
  ;;

  (* Generates the bipole of a formula from a generic initial sequent *)
  (* Considering the formula is chosen from gamma *)
  let bipole f =
    if Term.isBipole f then
      (* TODO: normalize the specifications. Do this in a more elegant way!! *)
      (* Note: there is a copy of this code in permutation.ml *)
      let rec instantiate_ex spec constLst = match spec with
	| EXISTS(s, i, f) ->
	  let constant = CONST (List.hd constLst) in
	  let newf = Norm.hnorm (APP (ABS (s, 1, f), [constant])) in
	  instantiate_ex newf (List.tl constLst)
	| _ -> (spec, constLst)
      in
      let constLst = ["b"; "a"; "d"; "c"; "e"] in
      let (fnorm, _) = instantiate_ex f constLst in
      let context = ContextSchema.createFresh () in
      let sequent = SequentSchema.createAsyn context [] in
      let constraints = Constraints.inEndSequent fnorm context in
      deriveBipole sequent fnorm constraints
    else raise Not_bipole

  (* Generates the bipoles of a list of terms, and only the bipoles *)
  let get_bipoles formulas = List.fold_right (fun f acc -> try 
    (bipole f) @ acc
    with Not_bipole -> 
      print_endline ("The formula\n" ^ Prints.termToString f ^ 
      "\nis not a bipole. Skipping it...\n");
      acc
  ) formulas []

end;;

