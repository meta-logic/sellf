(* TODO: transform this into a module? *)
(* Giselle Machado Reis - 2012 *)

open Basic
open Term

(***************** SUBEXPONENTIALS ***************)

(* Hashtable with subexponentials' types ($gamma is the linear context and
 * $infty holds specifications) 
 *)
let subexTpTbl = Hashtbl.create 100 ;;

(* Hashtable with subexponentials' parcial order *)
(* Each subexponential holds those which are greater than it. *)
let (subexOrdTbl : (string, string) Hashtbl.t ) = Hashtbl.create 100 ;;

let addType s t = Hashtbl.add subexTpTbl s t ;;

let initialize () = 
  Hashtbl.clear subexTpTbl;
  addType "$gamma" LIN;
  addType "$infty" UNB;
  Hashtbl.clear subexOrdTbl 
;;

(* Returns the type of a subexponential *)
let type_of s = try 
  Hashtbl.find subexTpTbl s
  with Not_found -> failwith ("[ERROR] Subexponential "^s^" has no type defined.")
;;

(* Gets all the unbounded subexponentials and make them greater then s 
 * (put in s' order list) *)
let lt_unbounded s = let subexps = keys subexTpTbl in
  let rec get_unbounded lst = match lst with
    | [] -> ()
    | u :: t -> (match Hashtbl.find subexTpTbl s with
      | UNB -> Hashtbl.add subexOrdTbl s u; (get_unbounded t)
      | _ -> get_unbounded t
    )
  in get_unbounded subexps
;;

(* Checks if a subexponential s1 > s2 *)
let rec bfs root queue goal = match queue with
  | [] -> false
  | h :: t when h = root -> failwith "Circular dependency on subexponential order."
  | h :: t when h = goal -> true
  | h :: t -> bfs root (t @ Hashtbl.find_all subexOrdTbl h) goal
;;
let greater_than s1 s2 = bfs s2 (Hashtbl.find_all subexOrdTbl s2) s1 ;;

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
let erased_bang s = erased s (keys subexTpTbl) ;;
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
let empty_bang s = checked_empty s (keys subexTpTbl) ;;

(* Checks whether or not a subexponential can suffer weakening *)
let weak i = match type_of i with
  | UNB | AFF -> true
  | REL | LIN -> false
;;


