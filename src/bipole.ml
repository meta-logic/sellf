(**************************************)
(*                                    *)
(*      Derivation of a bipole        *)
(*                                    *)
(*  Giselle Machado Reis              *)
(*  2013                              *)
(*                                    *)
(**************************************)

open Sequent
open Term

(* Builds the possible bipoles from a formula in a sequent and a set of constraints *)
(* Generates the necessary further constraints. *)
(* Returns a list of pairs (proof tree * model) *)

(* Transforms a list ((ProofTreeSchema * Constraints list) list) into a list of *)
(* pairs consisting of a proof tree schema and a valid non-empty model *)
let toPairsProofModel bipoles = List.fold_right (fun (pt, cstrlst) acc ->
  List.fold_right (fun cs acc ->
    let nonemptymodels = List.filter (fun m -> not (Constraints.isEmpty m)) (Dlv.getModels cs) in
    (List.map (fun model -> (pt, model)) nonemptymodels) @ acc
  ) cstrlst acc
) bipoles []
;;

let deriveBipole seq form constr = 

  (* Initialize the proof tree *)
  let pt0 = ProofTreeSchema.create seq in

  (* decide on form and create the necessary constraints *)
  (* GR Note to self: Why don't I just check if the formula is there? Because it
  might be the case that I have to the the reasoning DLV does, namely, check if
  a context is the union of other and check if this formula is in any of the
  others and bla bla bla. Leaving this for DLV. *)
  let (pt1, decidecstr) = ProofTreeSchema.decide pt0 form "$gamma" in

  (* Initial constraints *)
  let constraints : Constraints.constraintset list ref = ref [(Constraints.union decidecstr constr)] in

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

exception Not_bipole

(* Generates the bipole of a formula from a generic initial sequent *)
(* Considering the formula is chosen from gamma *)
let bipole f =
  if isBipole f then
    let context = ContextSchema.createFresh () in
    let sequent = SequentSchema.createAsyn context [] in
    let constraints = Constraints.isIn f "$gamma" context in
    deriveBipole sequent f constraints 
  else raise Not_bipole
;;

