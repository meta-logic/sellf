(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *  
 *                                                                      * 
 * CODE FOR PROVING COHERENCE OF SEQUENT SYSTEMS' SPECIFICATION         *
 *                                                                      *
 * NOTE:                                                                *
 * - the predicates that map object-level formulas to meta-level        *
 *   atoms are 'lft' and 'rght'                                         *
 * - formulas from the object logic have type 'form'                    *
 * - terms from the object logic have type 'term'                       *
 * - specification formulas are saved on the context $infty             *
 * - procedures to check cut and initial coherence                      *
 *                                                                      *
 * Giselle Machado Reis - 2011                                          *
 *                                                                      *
  * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

open Term
open Boundedproofsearch
open Prints
open TypeChecker
open Staticpermutationcheck (* because I am reusing the list of cuts *)

let cutcoherent = ref true ;;
let initcoherent = ref true ;;

let ids : terms list ref = ref [] ;;

let addIdRule r = 
  ids := r :: !ids

(* The specifications of each connective are stored in a hash 
 * The key is the name of the predicate representing the connective *)
let lr_hash : ((string, (terms * terms)) Hashtbl.t) ref = ref (Hashtbl.create 100) ;;

let initialize () = 
  cutcoherent := true;
  initcoherent := true;
  Hashtbl.clear !lr_hash ;;

(* Operation for the case that there is more than one specification for one side *)
let addLSpec str t = try match Hashtbl.find !lr_hash str with
  | (ZERO, r) -> Hashtbl.replace !lr_hash str (t, r)
  | (l, r) -> Hashtbl.replace !lr_hash str (ADDOR(l, t), r) 
  with Not_found -> Hashtbl.add !lr_hash str (t, ZERO)

let addRSpec str t = try match Hashtbl.find !lr_hash str with
  | (l, ZERO) -> Hashtbl.replace !lr_hash str (l, t)
  | (l, r) -> Hashtbl.replace !lr_hash str (l, ADDOR(r, t)) 
  with Not_found -> Hashtbl.add !lr_hash str (ZERO, t)

let getFirstArgName p = match p with
  | APP(CONS(n), lst) -> begin match lst with
    | CONS(s) :: t -> s
    | APP(CONS(s), _) :: t -> s
    | _ -> failwith "Error while getting the name of a connective. Are you sure
    this is a introduction rule specification?"
  end
  | _ -> failwith "Function is not an application."

let processIntroRule t = 
  let rec getPred f = match f with 
    | TENSOR(NOT(prd), spc) -> prd
    | ABS(s, i, t) -> getPred t
    | _ -> failwith "Not expected formula in specification."
  in
  let rec getSpec f = match f with
    | TENSOR(NOT(prd), spc) -> spc
    | ABS(s, i, t) -> ABS(s, i, getSpec t)
    | NOT(prd) -> TOP (* Specification has no body. *)
    | _ -> failwith "Not expected formula in specification."
  in
  let (p, s) = getPred t, getSpec t in
  match p with
    | PRED("lft", p, _) -> addLSpec (getFirstArgName p) s
    | PRED("rght", p, _) -> addRSpec (getFirstArgName p) s
    | _ -> failwith "Valid predicates are 'lft' and 'right'."

let dirName = ref "" ;;

(* Transforms abstractions into universal quantifiers *)
let rec abs2forall f = match f with
  | ABS(s, i, t) -> FORALL(s, i, abs2forall t)
  | t -> t
;;

(* Procedure to actually check the coherence of a system *)

let checkInitCoher str (t1, t2) =
  (* Put axiom formulas on the context *)
  Context.clearInitial ();
  List.iter (fun e -> Context.store e "$infty") !ids;

  (*print_endline "Trying to prove initial coherence of:";
  print_endline (termToString t1);
  print_endline (termToString t2);*)
  let bt1 = QST(CONS("$infty"), t1) in
  let bt2 = QST(CONS("$infty"), t2) in
  (*print_endline "After applying question mark:";
  print_endline (termToString bt1);
  print_endline (termToString bt2);*)
  (* Assign deBruijn indices correctly, after the two formulas are joined *)
  let f0 = deBruijn true (PARR(bt1, bt2)) in
  (* Replace abstractions by universal quantifiers *)
  let f = abs2forall f0 in
  (*print_endline ("After transformation: "^(termToString f));*)
  prove f 4 (fun () ->
          print_string ("====> Connective "^str^" is initial-coherent.\n"); ()
        )  
        (fun () ->
          initcoherent := false;
          print_string ("x===> Connective "^str^" is not initial-coherent.\n");
        )
;;

let checkDuality str (t1, t2) =
  (* Put cut formulas on the context *)
  Context.clearInitial ();
  List.iter (fun e -> Context.store e "$infty") !cutRules;

  (*print_endline "Trying to prove duality of:";
  print_endline (termToString t1);
  print_endline (termToString t2);*)
  let nt1 = deMorgan (NOT(t1)) in
  let nt2 = deMorgan (NOT(t2)) in
  (*print_endline "After negation:";
  print_endline (termToString nt1);
  print_endline (termToString nt2);*)
  (* Assign deBruijn indices correctly, after the two formulas are joined *)
  let f0 = deBruijn true (PARR(nt1, nt2)) in
  (* Replace abstractions by universal quantifiers *)
  let f = abs2forall f0 in
  (*print_endline ("After transformation: "^(termToString f));*)
  prove f 4 (fun () ->
          print_string ("====> Connective "^str^" has dual specification.\n"); ()
        )  
        (fun () ->
          cutcoherent := false;
          print_string ("x===> Connective "^str^" does not have dual specifications.\n");
        )
;;

let check sysName =
  dirName := sysName;
  (*Hashtbl.iter checkDuality !lr_hash; *)
  Hashtbl.iter checkInitCoher !lr_hash;
  if !cutcoherent then print_string "\nThe system is cut coherent.\n"
  else print_string "\nThe system is NOT cut coherent.\n";
  if !initcoherent then print_string "\nThe system is initial coherent.\n"
  else print_string "\nThe system is NOT initial coherent.\n"
    
;;

