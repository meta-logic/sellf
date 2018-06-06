(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *  
 *                                                                      * 
 * CODE FOR PROVING COHERENCE OF SEQUENT SYSTEMS' SPECIFICATION         *
 *                                                                      *
 * NOTE:                                                                *
 * - the predicates that map object-level formulas to meta-level        *
 *   atoms are 'lft', 'rght', 'mlft' and 'mrght'                        *
 * - formulas from the object logic have type 'form'                    *
 * - terms from the object logic have type 'term'                       *
 * - specification formulas are saved on the context infty              *
 * - procedures to check cut and initial coherence                      *
 *                                                                      *
 * Giselle Reis - 2011                                                  *
 *                                                                      *
  * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

open Context
open Types
open Boundedproofsearch
open Prints
open TypeChecker

(* Procedure to actually check the coherence of a system *)

let checkInitCoher system_name connective_name (spec_left, spec_right) =
  Boundedproofsearch.file_name := (system_name^"_initCoh_"^connective_name); 
  (* Put axiom formulas on the context *)
  Context.createInitialCoherenceContext ();
  
  let spec_left_infty = QST(CONST("infty"), spec_left) in
  let spec_right_infty = QST(CONST("infty"), spec_right) in
  (* Assign deBruijn indices correctly, after the two formulas are joined *)
  let f0 = deBruijn (PARR(spec_left_infty, spec_right_infty)) in
  (* Replace abstractions by universal quantifiers *)
  let f = Term.abs2forall f0 in
    prove f 4 (fun () -> true) (fun () -> false)
;;

let checkDuality system_name connective_name (spec_left, spec_right) =
  Boundedproofsearch.file_name := system_name^"_cutCoh_"^connective_name; 
  (* Put cut formulas on the context *)
  Context.createCutCoherenceContext ();
  
  let spec_left_normalized = Term.nnf (NOT(spec_left)) in
  let spec_right_normalized = Term.nnf (NOT(spec_right)) in
  (* Assign deBruijn indices correctly, after the two formulas are joined *)
  let f0 = deBruijn (PARR(spec_left_normalized, spec_right_normalized)) in 
  (* Replace abstractions by universal quantifiers *)
  let f = Term.abs2forall f0 in
    prove f 4 (fun () -> true) (fun () -> false)
;;

let cutCoherence system_name =
  Hashtbl.fold (fun conn specs res -> 
    (checkDuality system_name conn specs) && res 
  ) Specification.lr_hash true
;;

let initialCoherence system_name =
  Hashtbl.fold (fun conn specs res -> 
    (checkInitCoher system_name conn specs) && res 
  ) Specification.lr_hash true
;;

