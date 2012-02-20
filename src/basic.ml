(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         * 
 * Auxiliary functions for basic data structures           * 
 *                                                         *
 * Giselle Machado Reis - 2012                             *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

open Prints

(******************* LISTS ************************)
(*
 * Auxiliary functions for lists.
 *)

(* TODO: there must be a smarter way of doing this... *)
(* Removes an element from a list *)
let rec remove_element a lst acc = 
  match lst with 
  | [] -> acc
  | a1 :: t when a1 = a -> acc @ t
  | b :: t -> remove_element a t (acc @ [b])
(* Important note: removes only the first occurence of the element *)
let rec remove elm lst = remove_element elm lst []
;;

(* Remove the elements of rem from the list lst *)
let rec removeLst rem lst = match rem with
  | [] -> lst
  | hd::tl -> removeLst tl (remove hd lst)

let make_first elm lst = elm :: (remove elm lst) ;;

(* Decides if an element e is in a list l *)
let rec in_list l e = try match List.hd l with
    | h when h = e -> true
    | _ -> in_list (List.tl l) e
    with Failure "hd" -> false
;;

(******************* HASHTABLES ************************)
(*
 * Auxiliary functions for hashtables.
 *)

(* Get all the keys from a hash table, including duplicates *)
let keys ht = Hashtbl.fold (fun key data accu -> key :: accu) ht [] ;;

let print_hashtbl h = print_string "\nHashTable:\n";
  let keylst = keys h in
  let rec print_h lst = 
    match lst with
      | [] -> print_string "\n"
      | k :: t -> 
        print_string ("["^k^"] "); 
        print_list_terms (Hashtbl.find h k); 
        print_newline (); print_h t
  in print_h keylst
;;


