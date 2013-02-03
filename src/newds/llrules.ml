(**************************************)
(*                                    *)
(*        Linear Logic Rules          *)
(*                                    *)
(*  Giselle Machado Reis              *)
(*  2013                              *)
(*                                    *)
(**************************************)

type rule = 
  | TENSORRULE 
  | ADDOR1RULE
  | ADDOR2RULE
  | PARRRULE
  | WITHRULE
  | BANGRULE
  | HBANGRULE
  | QSTRULE
  | FORALLRULE
  | EXISTSRULE
  | TOPRULE
  | BOTRULE
  | ONERULE
  | INIT
  | DECIDE
  | RELEASEUP
  | RELEASEDOWN


(* Implement apply rules for each one. It should return a list of sequents
 * (premisses) and take a sequent as a parameter (conclusion). 
 * In addition, when the rule is being applied to an abstract sequent, it should
 * return a list of constraints... is this possible? The types won't match :( *)

(* Implement only for the permutation case first... *)

(* Return sequents or the updated prooftree?? *)
let applyTensorRule pt TENSOR(f1, f2) = match ProofTree.getConclusion pt with
  | ABSSEQ(s) =>
  (* Make sure the main formula is in the goals. Split the context and create
   * the constraints. Create the premisse sequents. Update the prooftree. Return
   * the prooftree and constraints. *)

