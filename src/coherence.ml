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
 * Giselle Machado Reis - 2011                                          *
 *                                                                      *
  * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

open Context
open Types
open Boundedproofsearch
open Prints
open TypeChecker

let cutcoherent = ref true ;;
let initcoherent = ref true ;;

(* Procedure to actually check the coherence of a system *)

let checkInitCoher system_name connective_name (spec_left, spec_right) =
  Boundedproofsearch.file_name := (system_name^"_initCoh_"^connective_name); 
  (* Put axiom formulas on the context *)
  Context.createInitialCoherenceContext ();
  
  let spec_left_infty = QST(CONST("infty"), spec_left) in
  let spec_right_infty = QST(CONST("infty"), spec_right) in
  (* print_endline "Proving initial coherence of:";
  print_endline (termToString spec_left_infty);
  print_endline (termToString spec_right_infty); *)
  (* Assign deBruijn indices correctly, after the two formulas are joined *)
  let f0 = deBruijn true (PARR(spec_left_infty, spec_right_infty)) in
  (* Replace abstractions by universal quantifiers *)
  let f = Term.abs2forall f0 in
  prove f 4 (fun () ->
          print_string ("====> Connective "^connective_name^" is initial-coherent.\n"); ()
        )  
        (fun () ->
          initcoherent := false;
          print_string ("x ==> Connective "^connective_name^" is not initial-coherent.\n");
        )
;;

let checkDuality system_name connective_name (spec_left, spec_right) =
  Boundedproofsearch.file_name := system_name^"_cutCoh_"^connective_name; 
  (* Put cut formulas on the context *)
  Context.createCutCoherenceContext ();
  
  let spec_left_normalized = Term.nnf (NOT(spec_left)) in
  let spec_right_normalized = Term.nnf (NOT(spec_right)) in
  (* print_endline "Proving cut coherence of:";
  print_endline (termToString spec_left_normalized);
  print_endline (termToString spec_right_normalized); *)
  (* Assign deBruijn indices correctly, after the two formulas are joined *)
  let f0 = deBruijn true (PARR(spec_left_normalized, spec_right_normalized)) in 
  (* Replace abstractions by universal quantifiers *)
  let f = Term.abs2forall f0 in
  prove f 4 (fun () ->
          print_string ("====> Connective "^connective_name^" has dual specification.\n"); ()
        )  
        (fun () ->
          cutcoherent := false;
          print_string ("x ==> Connective "^connective_name^" does not have dual specifications.\n");
        )
;;

let cutCoherence system_name =
  cutcoherent := true;
  Hashtbl.iter (checkDuality system_name) Specification.lr_hash;
  if !cutcoherent then print_string "\nTatu coud prove that the system is cut coherent.\n"
  else print_string "\nThe system is NOT cut coherent.\n";
;;

let initialCoherence system_name =
  initcoherent := true;
  Hashtbl.iter (checkInitCoher system_name) Specification.lr_hash;
  if !initcoherent then print_string "\nTatu could prove that the system is initial coherent.\n"
  else print_string "\nThe system is NOT initial coherent.\n"
;;

