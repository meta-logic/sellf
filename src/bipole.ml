(**************************************)
(*                                    *)
(*      Derivation of a bipole        *)
(*                                    *)
(*  Giselle Machado Reis              *)
(*  2013                              *)
(*                                    *)
(**************************************)

open ProofTreeSchema

(* Builds a bipole from a sequent and a formula and a set of constraints *)
(* Generates the necessary constraints. *)

let deriveBipole seq form constr = 

  (* Initialize the proof tree *)
  let pt0 = ProofTreeSchema.create seq in

  (* decide on form and create the necessary constraints *)
  (* Note to self: Why don't I just check if the formula is there? Because it
  might be the case that I have to the the reasoning DLV does, namely, check if
  a context is the union of other and check if this formula is in any of the
  others and bla bla bla. Leaving this for DLV. *)
  let (pt1, decidecstr) = ProofTreeSchema.decide pt0 form "$gamma" in

  (* Builds the derivation of f as a bipole (one positive and one negative
  phase). 'acc' holds the resulting pairs (prooftree * constraints list)?? *)
  let derive (prooftree, constraintlst) acc(?) = 
    let conclusion = ProofTreeSchema.getConclusion prooftree in
    match (SequentSchema.getPhase conclusion, SequentSchema.getGoals) with

    | SYNC, [f] -> match Term.observe f with
      (* Release rule *)
      | WITH(_,_)
      | PARR(_,_)
      | TOP
      | BOT
      | FORALL(_,_)
      | QST(_) ->
        let (pt, c) = ProofTreeSchema.releaseDown pt
        derive (pt, constraintlst.map(fun cst -> Constraint.add cst c))

    | ASYN, hd::tl -> 


  in
  derive (pt1, [(decidecstr @ constr)]) []

