(* 
 * CODE FOR PROVING COHERENCE OF SEQUENT SYSTEMS' SPECIFICATION
 *
 * NOTE:
 * - the predicates that map object-level formulas to meta-level atoms are 'lft'
 * and 'rght'
 *)

open Term
open Structs
open Common
open Blindsearch
open Interpreter
open Prints

(* Indicates if this is the specification of a sequent calculus system *)
let seqcalc = ref true ;;

(* The specifications of each connective are stored in a hash 
 * The key is the name of the predicate representing the connective *)
let lr_hash : ((string, (terms * terms)) Hashtbl.t) ref = ref (Hashtbl.create 100) ;;

(* Operation for the case that there is more than one specification for one side *)
let addLSpec str t = try match Hashtbl.find !lr_hash str with
  | (ONE, r) -> Hashtbl.replace !lr_hash str (t, r)
  | (l, r) -> Hashtbl.replace !lr_hash str (ADDOR(l, t), r) 
  with Not_found -> Hashtbl.add !lr_hash str (t, ONE)

let addRSpec str t = try match Hashtbl.find !lr_hash str with
  | (l, ONE) -> Hashtbl.replace !lr_hash str (l, t)
  | (l, r) -> Hashtbl.replace !lr_hash str (l, ADDOR(r, t)) 
  with Not_found -> Hashtbl.add !lr_hash str (ONE, t)

let getFirstArgName p = match p with
  | APP(CONS(n), lst) -> begin match lst with
    | CONS(s) :: t -> s
    | APP(CONS(s), _) :: t -> s
    | _ -> failwith "Error while getting the name of an application."
  end
  | _ -> failwith "Function is not an application."

let addSpec t = 
  let rec getTerms f = match f with 
    | TENSOR(NOT(prd), spc) -> (prd, spc)
    | ABS(s, i, t) -> getTerms t
    | _ -> failwith "Not expected formula in specification."
  in
  let (p, s) = getTerms t in
  match p with
    | PRED("lft", p, _) -> addLSpec (getFirstArgName p) s
    | PRED("rght", p, _) -> addRSpec (getFirstArgName p) s
    | _ -> seqcalc := false

(* Procedure to actually check the coherence of a system *)

let coherent = ref true ;;

let checkDuality str (t1, t2) = 
  print_endline "Trying to prove duality of:";
  print_term t1; print_newline ();
  print_term t2; print_newline ();
  let nt1 = deMorgan (NOT(t1)) in
  let nt2 = deMorgan (NOT(t2)) in
  print_endline "After negation:";
  print_term nt1; print_newline ();
  print_term nt2; print_newline ();
  add_goals (PARR(nt1, nt2));
  prove 4 (fun () -> 
  (*solve (fun () -> *)
          if (empty_nw ()) then begin 
          print_string ("Connective "^str^" has dual specification.\n");
          end
          else (Structs.last_fail ())
        )  
        (fun () ->
          coherent := false;
          print_string ("Connective "^str^" does not have dual specifications.\n");
        ) ()

let check () = 
  Hashtbl.iter checkDuality !lr_hash; 
  if !coherent then print_string "\nThe system is coherent.\n"
  else print_string "\nThe system in NOT coherent.\n"
;;

