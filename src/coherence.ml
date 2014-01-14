(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *  
 *                                                                      * 
 * CODE FOR PROVING COHERENCE OF SEQUENT SYSTEMS' SPECIFICATION         *
 *                                                                      *
 * NOTE:                                                                *
 * - the predicates that map object-level formulas to meta-level        *
 *   atoms are 'lft', 'rght', 'mlft' and 'mrght'                        *
 * - formulas from the object logic have type 'form'                    *
 * - terms from the object logic have type 'term'                       *
 * - specification formulas are saved on the context $infty             *
 * - procedures to check cut and initial coherence                      *
 *                                                                      *
 * Giselle Machado Reis - 2011                                          *
 *                                                                      *
  * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

open Context
open Term
open Boundedproofsearch
open Prints
open TypeChecker

let cutcoherent = ref true ;;
let initcoherent = ref true ;;

let initialize () = 
  cutcoherent := true;
  initcoherent := true
;;

(* Procedure to actually check the coherence of a system *)

let system_name = ref "" ;;

let checkInitCoher str (t1, t2) =
  file_name := ((!system_name)^"_initCoh_"^str); 
  (* Put axiom formulas on the context *)
  Context.createInitialCoherenceContext ();
  
  let bt1 = QST(CONST("$infty"), t1) in
  let bt2 = QST(CONST("$infty"), t2) in
  (* print_endline "Proving initial coherence of:";
  print_endline (termToString bt1);
  print_endline (termToString bt2); *)
  (* Assign deBruijn indices correctly, after the two formulas are joined *)
  let f0 = deBruijn true (PARR(bt1, bt2)) in
  (* Replace abstractions by universal quantifiers *)
  let f = abs2forall f0 in
  prove f 4 (fun () ->
          print_string ("====> Connective "^str^" is initial-coherent.\n"); ()
        )  
        (fun () ->
          initcoherent := false;
          print_string ("x===> Connective "^str^" is not initial-coherent.\n");
        )
;;

let checkDuality str (t1, t2) =
  file_name := ((!system_name)^"_cutCoh_"^str); 
  (* Put cut formulas on the context *)
  Context.createCutCoherenceContext ();
  
  let nt1 = nnf (NOT(t1)) in
  let nt2 = nnf (NOT(t2)) in
  (* print_endline "Proving cut coherence of:";
  print_endline (termToString nt1);
  print_endline (termToString nt2); *)
  (* Assign deBruijn indices correctly, after the two formulas are joined *)
  let f0 = deBruijn true (PARR(nt1, nt2)) in 
  (* Replace abstractions by universal quantifiers *)
  let f = abs2forall f0 in
  prove f 4 (fun () ->
          print_string ("====> Connective "^str^" has dual specification.\n"); ()
        )  
        (fun () ->
          cutcoherent := false;
          print_string ("x===> Connective "^str^" does not have dual specifications.\n");
        )
;;

(* TODO: put proper system name *)
let cutCoherence () =
  system_name := "proofsTex/coherence/proof";
  Hashtbl.iter checkDuality Specification.lr_hash;
  if !cutcoherent then print_string "\nTatu coud prove that the system is cut coherent.\n"
  else print_string "\nThe system is NOT cut coherent.\n";
;;

let initialCoherence () =
  system_name := "proofsTex/coherence/proof";
  Hashtbl.iter checkInitCoher Specification.lr_hash;
  if !initcoherent then print_string "\nTatu could prove that the system is initial coherent.\n"
  else print_string "\nThe system is NOT initial coherent.\n"
;;

