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
  let pt1 = ProofTreeSchema.decide pt0 f "$gamma" in

  let derive f prooftree

