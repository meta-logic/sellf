(****************************************)
(*                                      *)
(*          Specification               *)
(* Holds the information of a system's  *) 
(* specification (types, rules, etc.)   *)
(*                                      *)
(*  Giselle Machado Reis                *)
(*  2012                                *)
(*                                      *)
(****************************************)

open Term

(* Info from the .sig file *)

let kindTbl : (string, basicTypes) Hashtbl.t = Hashtbl.create 100 ;;
let typeTbl : (string, types) Hashtbl.t = Hashtbl.create 100 ;;

let isKindDeclared name = try match Hashtbl.find kindTbl name with
  | _ -> true
  with Not_found -> false

let isTypeDeclared name = try match Hashtbl.find typeTbl name with
  | _ -> true
  with Not_found -> false

let addTypeTbl name entry = Hashtbl.add typeTbl name entry 

let addKindTbl entry = 
	match entry with
	| TINT -> NONE
	| TPRED -> NONE
	| TKIND (k) -> (
    match (isKindDeclared k) with
	    | false -> Hashtbl.add kindTbl k (TKIND (k)); NONE
			| true -> SOME (k)
    )
	| _ -> NONE
;;

(* Info from the .pl file *)

let structRules : terms list ref = ref [] ;;
let cutRules : terms list ref = ref [] ;;
let introRules : terms list ref = ref [] ;;
let axioms : terms list ref = ref [] ;;

let addStructRule r = 
  let er = abs2exists r in
  structRules := er :: !structRules

let addCutRule r = 
  let er = abs2exists r in
  cutRules := er :: !cutRules

let addIntroRule r =
  let er = abs2exists r in
  introRules := er :: !introRules

let addAxiom r =
  let er = abs2exists r in
  axioms := er :: !axioms

(* The left and right specifications (bodies) of each introduction rule are stored as a
   pair in a hashtable, where the key is the predicate's name *)
let lr_hash : (string, (terms * terms)) Hashtbl.t = Hashtbl.create 100 ;;

(* Operation for the case that there is more than one specification for one side *)
let addLSpec str t = try match Hashtbl.find lr_hash str with
  | (ZERO, r) -> Hashtbl.replace lr_hash str (t, r)
  | (l, r) -> Hashtbl.replace lr_hash str (ADDOR(l, t), r) 
  with Not_found -> Hashtbl.add lr_hash str (t, ZERO)

let addRSpec str t = try match Hashtbl.find lr_hash str with
  | (l, ZERO) -> Hashtbl.replace lr_hash str (l, t)
  | (l, r) -> Hashtbl.replace lr_hash str (l, ADDOR(r, t)) 
  with Not_found -> Hashtbl.add lr_hash str (ZERO, t)

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
    | NOT(prd) -> prd
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
    | PRED("mlft", p, _) -> addLSpec (getFirstArgName p) s
    | PRED("mrght", p, _) -> addRSpec (getFirstArgName p) s
    | _ -> failwith "Valid predicates are 'lft' or 'right' or 'mlft' or 'mrght'."
;;

let initialize () =
  structRules := [];
  cutRules := [];
  introRules := []; 
  axioms := [];
  Hashtbl.clear kindTbl;
  Hashtbl.clear typeTbl;
  Hashtbl.clear lr_hash;
  (* Bult-in kind for formulas *)
  Hashtbl.add kindTbl "o" (TPRED) ;
  (* Built-in types and kinds for systems' specification *)
  Hashtbl.add kindTbl "form" (TKIND("form")) ;
  Hashtbl.add kindTbl "term" (TKIND("term")) ;
  Hashtbl.add kindTbl "world" (TKIND("world")) ;
  addTypeTbl "lft" (ARR (TBASIC (TKIND("form")), TBASIC (TPRED))) ;  (* type lft form -> o. *)
  addTypeTbl "rght" (ARR (TBASIC (TKIND("form")), TBASIC (TPRED))) ; (* type rght form -> o. *) 
  addTypeTbl "mlft" (ARR (TBASIC (TKIND("form")), (ARR (TBASIC (TKIND("world")), TBASIC (TPRED))))) ;  (* type mlft form -> world -> o. *)
  addTypeTbl "mrght" (ARR (TBASIC (TKIND("form")), (ARR (TBASIC (TKIND("world")), TBASIC (TPRED))))) ;  (* type mrght form -> world -> o. *)
;;
