(**************************************)
(*                                    *)
(*         Subexponentials            *)
(*                                    *)
(*  Giselle Machado Reis              *)
(*  2012                              *)
(*                                    *)
(**************************************)

open Term

type subexp = 
| UNB (* unbounded: contraction and weakening *)
| AFF (* affine: weakening *)
| REL (* relevant: contraction *)
| LIN (* linear *)

type arity = 
  | MANY
  | SINGLE

type side = 
  | LEFT
  | RIGHT
  | RIGHTLEFT

(* Hashtable with subexponentials' types ($gamma is the linear context and
 * $infty holds specifications) 
 *)
let typeTbl = Hashtbl.create 100 ;;  

(* Hashtable with subexponentials' parcial order *)
(* Each subexponential holds those which are greater than it. *)
let orderTbl : (string, string) Hashtbl.t = Hashtbl.create 100 ;;

(* Hashtable with subexponentials context types *)
(* Context type: (formulas description, side) *)
type ctxType = (arity * side) ;;
let ctxTbl : (string, ctxType) Hashtbl.t = Hashtbl.create 100 ;;

let getCtxSide s = try match Hashtbl.find ctxTbl s with
  | (_, side) -> side
  with Not_found -> failwith ("Subexponential " ^ s ^ " has no type information.")
;;

let getCtxArity s = try match Hashtbl.find ctxTbl s with
  | (t, _) -> t
  with Not_found -> failwith ("Subexponential " ^ s ^ " has no type information.")
;;

let addType s t = Hashtbl.add typeTbl s t ;;

let isSubexponentialDeclared name = try match Hashtbl.find typeTbl name with
  | _ -> true
  with Not_found -> false

let initialize () = 
  Hashtbl.clear typeTbl;
  addType "$gamma" LIN;
  addType "$infty" UNB;
  Hashtbl.clear orderTbl 
;;

(* Returns the names of all subexponentials *)
let getAll () = Hashtbl.fold (fun key data acc -> key :: acc) typeTbl [] ;;

(* Returns the names of all subexponentials that are specified to be printed *)
let getAllValid () = Hashtbl.fold (fun key data acc -> key :: acc) ctxTbl [] ;;

(* Returns the type of a subexponential *)
let type_of s = try 
  Hashtbl.find typeTbl s
  with Not_found -> failwith ("[ERROR] Subexponential "^s^" has no type defined.")
;;

(* Gets all the unbounded subexponentials and make them greater then s 
 * (put in s' order list) *)
let lt_unbounded s =
  let rec get_unbounded lst = match lst with
    | [] -> ()
    | u :: t -> (match Hashtbl.find typeTbl s with
      | UNB -> Hashtbl.add orderTbl s u; (get_unbounded t)
      | _ -> get_unbounded t
    )
  in get_unbounded (getAll ())
;;

(* Checks if a subexponential s1 > s2 *)
let rec bfs root queue goal = match queue with
  | [] -> false
  | h :: t when h = root -> failwith "Circular dependency on subexponential order."
  | h :: t when h = goal -> true
  | h :: t -> bfs root (t @ Hashtbl.find_all orderTbl h) goal
;;
let greater_than s1 s2 = 
  (* $infty should be greater than everyone *)
  if s1 = "$infty" then true
  else bfs s2 (Hashtbl.find_all orderTbl s2) s1 ;;

(* Returns a list with all subexponentials from idxs that will have their 
 * formulas erased if !s is applied. *)
let rec erased s idxs = match idxs with
  | [] -> []
  | i::t -> 
    match type_of i with
      | UNB | AFF -> 
        if i = "$infty" || i = s || (greater_than i s) then erased s t
        else i::(erased s t)
      | _ -> erased s t
;;
let erased_bang s = erased s (getAll ()) ;;
(* Returns a list with all subexponentials from idxs that will be checked 
 * for emptiness if !s is applied. *)
let rec checked_empty s idxs = match idxs with
  | [] -> []
  | i::t -> 
    match type_of i with
      | REL | LIN -> 
        if i = "$gamma" || i = s || (greater_than i s) then checked_empty s t
        else i::(checked_empty s t)
      | _ -> checked_empty s t
;;
let empty_bang s = checked_empty s (getAll ()) ;;

(* Checks whether or not a subexponential can suffer weakening *)
let weak i = match type_of i with
  | UNB | AFF -> true
  | REL | LIN -> false
;;

let typeAsString s = match type_of s with
  | LIN -> "lin"
  | UNB -> "unb"
  | REL -> "rel"
  | AFF -> "aff"

(* Checks if a subexponential is on the same side as pred *)
let isSameSide sub str = try match (getCtxSide sub, str) with
  | (RIGHTLEFT, _) -> true
  | (RIGHT, "rght") -> true
  | (LEFT, "lft") -> true
  | _ -> false
  with _ -> false

  
