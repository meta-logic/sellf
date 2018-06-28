(****************************************)
(*                                      *)
(*          Specification               *)
(* Holds the information of a system's  *) 
(* specification (types, rules, etc.)   *)
(*                                      *)
(*  Giselle Reis                        *)
(*                                      *)
(****************************************)

open Types
open Term

module type SPECIFICATION = sig

  type specification = {
    name : string;
    (* From .sig file *)
    kindTbl : (string, basicTypes) Hashtbl.t;
    typeTbl : (string, types) Hashtbl.t;
    (* From .pl file *)
    structRules : terms list;
    cutRules : terms list;
    introRules : terms list;
    axioms : terms list;
    (* The left and right specifications (bodies) of each introduction rule are stored as a
      pair in a hashtable, where the key is the predicate's name *)
    lr_hash : (string, (terms * terms)) Hashtbl.t;
  }

  val create : string * (string, basicTypes) Hashtbl.t * (string, types) Hashtbl.t * terms list * terms list * terms list * terms list -> specification
  val isKindDeclared : specification -> string -> bool
  val isTypeDeclared : specification -> string -> bool
  val getTypes : specification -> (string, types) Hashtbl.t
  val getLRHash : specification -> (string, (terms * terms)) Hashtbl.t
  val getRules : specification -> terms list
  val getStructRules : specification -> terms list
  val getCutRules : specification -> terms list
  val getIntroRules : specification -> terms list
  val getAxioms : specification -> terms list
  val getIntroRulesNames : specification -> string list
  val getSpecificationOf : specification -> string -> terms
  val getUserTypes : specification -> (string * types) list

end ;;

module Specification : SPECIFICATION = struct
  
  type specification = {
    name : string;
    (* From .sig file *)
    kindTbl : (string, basicTypes) Hashtbl.t;
    typeTbl : (string, types) Hashtbl.t;
    (* From .pl file *)
    structRules : terms list;
    cutRules : terms list;
    introRules : terms list;
    axioms : terms list;
    (* The left and right specifications (bodies) of each introduction rule are stored as a
      pair in a hashtable, where the key is the predicate's name *)
    lr_hash : (string, (terms * terms)) Hashtbl.t;
  }

  let processIntroRules l =
    let lr = Hashtbl.create 100 in
    let rec getBody f = match f with
      | TENSOR(NOT(prd), spc) -> spc
      | ABS(s, i, t) -> ABS(s, i, getBody t)
      | NOT(prd) -> TOP (* Specification has no body. *)
      | _ -> failwith ("[ERROR] Formula does not correspond to introduction rule: " ^ (Prints.termToString f))
    in
    let addLSpec str t = try match Hashtbl.find lr str with
      | (ZERO, r) -> Hashtbl.replace lr str (t, r)
      | (l, r) -> Hashtbl.replace lr str (ADDOR(l, t), r) 
      with Not_found -> Hashtbl.add lr str (t, ZERO)
    in  
    let addRSpec str t = try match Hashtbl.find lr str with
      | (l, ZERO) -> Hashtbl.replace lr str (l, t)
      | (l, r) -> Hashtbl.replace lr str (l, ADDOR(r, t)) 
      with Not_found -> Hashtbl.add lr str (ZERO, t)
    in 
    List.iter (fun f ->
      match getSide f with
        | "l" -> addLSpec (getConnectiveName f) (getBody f)
        | "r" -> addRSpec (getConnectiveName f) (getBody f)
        | _ -> failwith "Valid predicates are 'lft' or 'right' or 'mlft' or 'mrght'."
    ) l; lr
  
  let create (n, kt, tt, s, c, i, a) =
    let sdb = List.map (fun f -> Term.abs2exists (TypeChecker.deBruijn f)) s in
    let cdb = List.map (fun f -> Term.abs2exists (TypeChecker.deBruijn f)) c in
    let idb = List.map (fun f -> Term.abs2exists (TypeChecker.deBruijn f)) i in
    let adb = List.map (fun f -> Term.abs2exists (TypeChecker.deBruijn f)) a in
    let _ = List.iter (fun f -> let _ = TypeChecker.typeCheck f tt in ()) (s @ c @ i @ a) in
    let lr = processIntroRules i in
    { 
      name = n;
      kindTbl = kt;
      typeTbl = tt;
      structRules = sdb;
      cutRules = cdb;
      introRules = idb;
      axioms = adb;
      lr_hash = lr
    }

  let isKindDeclared spec name = Hashtbl.mem spec.kindTbl name

  let isTypeDeclared spec name = Hashtbl.mem spec.typeTbl name

  let getTypes spec = spec.typeTbl

  let getLRHash spec = spec.lr_hash

  let getRules spec = spec.introRules @ spec.structRules @ spec.cutRules @ spec.axioms
  
  let getStructRules spec = spec.structRules
  
  let getCutRules spec = spec.cutRules
  
  let getIntroRules spec = spec.introRules

  let getAxioms spec = spec.axioms
  
  let getIntroRulesNames spec = List.map (fun f -> getRuleName f) spec.introRules
  
  (* Given a name of a rule, returns its specification. *)
  let getSpecificationOf spec name = 
    try
      List.find (fun f -> getRuleName f = name) spec.introRules
    with Not_found -> failwith ("Specification of rule " ^ name ^ " not found")
  
  (* Returns only the types declared by the user in the .sig file (as a list of pairs) *)
  let getUserTypes spec = Hashtbl.fold (fun name tp acc ->
    match name with
      | "lft" | "rght" | "mlft" | "mrght" -> acc
      | _ -> (name, tp) :: acc
    ) spec.typeTbl []

end ;;

