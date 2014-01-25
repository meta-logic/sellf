(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         * 
 * Auxiliary functions for basic data structures           * 
 *                                                         *
 * Giselle Machado Reis - 2012                             *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

(******************* LISTS ************************)
(*
 * Auxiliary functions for lists.
 *)

module Basic = struct
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

(* Cartesian product of a list of lists *)
let rec cartesianProduct lst = match lst with
  | [] -> [[]]
  | hd :: tl -> List.concat ( List.map (fun l -> List.map (fun el -> el :: l) hd) (cartesianProduct tl) )
end;;

