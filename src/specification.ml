(****************************************)
(*                                      *)
(*          Specification               *)
(* Holds the information of a system's  *) 
(* specification (types, rules, etc.)   *)
(*                                      *)
(*  Giselle Reis                        *)
(*  2012                                *)
(*                                      *)
(****************************************)

open Types
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

let addKindTbl entry = match entry with
  | TINT -> None
  | TPRED -> None
  | TKIND (k) -> begin
    match (isKindDeclared k) with
      | false -> Hashtbl.add kindTbl k (TKIND (k)); None
      | true -> Some (k)
    end
  | _ -> None
;;

(* Info from the .pl file *)

let structRules : terms list ref = ref [] ;;
let cutRules : terms list ref = ref [] ;;
let introRules : terms list ref = ref [] ;;
let axioms : terms list ref = ref [] ;;

let others : terms list ref = ref [] ;;

let addStructRule r = 
  let er = abs2exists r in
  structRules := !structRules @ [er]

let addCutRule r = 
  let er = abs2exists r in
  cutRules := !cutRules @ [er]

let addIntroRule r =
  let er = abs2exists r in
  introRules := !introRules @ [er]

let addAxiom r =
  let er = abs2exists r in
  axioms := !axioms @ [er]

let addOthers f = 
  let ef = abs2exists f in
  others := !others @ [ef]

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

(* Returns the predicate in the head of a specification. 
 * TODO: if there are existential quantifiers, the DB indices are messed up with
 * this method... *)
let rec getHeadPredicate f = match f with 
  | TENSOR(NOT(prd), spc) -> prd
  | EXISTS(s, i, t) -> getHeadPredicate t
  | NOT(prd) -> prd
  | PRED(_, _, _) -> f
  | _ -> failwith ("Not expected formula in specification: " ^ Prints.termToString f)
;;

(* Returns the side of the introduction rule *)
let rec getSide f = match getHeadPredicate f with 
  | PRED("lft", _, _) -> "l"
  | PRED("rght", _, _) -> "r"
  | PRED("mlft", _, _) -> "l"
  | PRED("mrght", _, _) -> "r"
  | _ -> failwith ("No side information available (predicate not corresponding to a specification's head or not a predicate): " ^ Prints.termToString f)
;;

let getConnectiveName f = match getHeadPredicate f with
  | PRED(_, APP(CONST(_), args), _) -> begin match args with
    | CONST(s) :: t -> s
    | APP(CONST(s), _) :: t -> s
    | _ -> "noname"
    (* TODO FIXME commented out because this method is sometimes called for structural rules *)
    (*failwith "Error while getting the name of a connective. Are you sure this is an introduction rule specification?"*)
    end
  | _ -> failwith ("Error getting the name of a connective: " ^ (Prints.termToString (getHeadPredicate f)))
;;

let getObjectLogicMainFormula f = match getHeadPredicate f with
  | PRED(_, APP(CONST(_), h::tl), _) -> h
  | _ -> failwith ("Error getting the object logic's main formula from a specification: " ^ (Prints.termToString (getHeadPredicate f)))
;;

let getRuleName f = (getConnectiveName f) ^ "_" ^ (getSide f) ;; 

let getAllRulesName () = 
  let formulas = !others @ !introRules in
  List.map (fun f -> getRuleName f) formulas
;;

(* Given a name of a rule, returns its specification.
 * NOTE: relies on the fact that the formulas in the lists never change order.
 *)
let getSpecificationOf name = 
  let formulas = !others @ !introRules in
  try
    List.find (fun f -> getRuleName f = name) formulas
  with Not_found -> failwith ("Specification of rule " ^ name ^ " not found")
;;

let processIntroRule t = 
  let rec getBodyFormula f = match f with
    | TENSOR(NOT(prd), spc) -> spc
    | ABS(s, i, t) -> ABS(s, i, getBodyFormula t)
    | NOT(prd) -> TOP (* Specification has no body. *)
    | _ -> failwith "Not expected formula in specification."
  in
  match getSide t with
    | "l" -> addLSpec (getConnectiveName t) (getBodyFormula t)
    | "r" -> addRSpec (getConnectiveName t) (getBodyFormula t)
    | _ -> failwith "Valid predicates are 'lft' or 'right' or 'mlft' or 'mrght'."
;;

let getAllRules () = !others @ !introRules @ !structRules @ !cutRules @ !axioms ;;

(* Returns only the types declared by the user in the .sig file (as a list of pairs) *)
let getUserTypes () = Hashtbl.fold (fun name tp acc ->
  match name with
    | "lft" | "rght" | "mlft" | "mrght" -> acc
    | _ -> (name, tp) :: acc
  ) typeTbl []

let initialize () =
  structRules := [];
  cutRules := [];
  introRules := []; 
  axioms := [];
  others := [];
  Hashtbl.clear kindTbl;
  Hashtbl.clear typeTbl;
  Hashtbl.clear lr_hash;
  (* Bult-in kind for formulas *)
  Hashtbl.add kindTbl "o" (TPRED) ;
  (* Built-in types and kinds for systems' specification *)
  Hashtbl.add kindTbl "form" (TKIND("form")) ;
  Hashtbl.add kindTbl "term" (TKIND("term")) ;
  Hashtbl.add kindTbl "world" (TKIND("world")) ;
  addTypeTbl "lft" (ARR (TCONST (TKIND("form")), TCONST (TPRED))) ;  (* type lft form -> o. *)
  addTypeTbl "rght" (ARR (TCONST (TKIND("form")), TCONST (TPRED))) ; (* type rght form -> o. *) 
  addTypeTbl "mlft" (ARR (TCONST (TKIND("form")), (ARR (TCONST (TKIND("world")), TCONST (TPRED))))) ;  (* type mlft form -> world -> o. *)
  addTypeTbl "mrght" (ARR (TCONST (TKIND("form")), (ARR (TCONST (TKIND("world")), TCONST (TPRED))))) ;  (* type mrght form -> world -> o. *)
;;

