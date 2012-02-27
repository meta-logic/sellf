(*
This module implements the static conditions detailed in Section 5 of the paper
below for determining whether an object rule permutes over aanother object rule.
This analysis is necessary for determining whether an object-logic proof with cuts
can be transformed into a proof with principal cuts only.

"Extended Framework for Specifying and Reasoning about Proof Systems
by Vivek Nigam, Elaine Pimentel, and Giselle Reis"

*)

open Basic
open Term
open Subexponentials

(* Assuming that the cut has the following shape:

    exists A. !a ?b lft{A} tensor !c ?d right{A}
*)

let rec get_subexp_prefix rule =
let rec get_subexp_from_monopole mono = 
  match mono with
  | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_) -> []
  | PARR(b1,b2) | WITH(b1,b2) -> 
    List.append (get_subexp_from_monopole b1) (get_subexp_from_monopole b2)
  | QST(CONS(sub),b2) -> [SOME(sub)]
  | FORALL(_,_,b) -> (get_subexp_from_monopole b)
  | _ -> failwith "Unexpected term in a monopole."
  in
  match rule with
  | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_)  -> []
  | TENSOR(b1, b2) | ADDOR(b1,b2) -> 
      List.append (get_subexp_prefix b1) (get_subexp_prefix b2)
  | BANG(CONS(sub),b) -> [SOME(sub) :: (get_subexp_from_monopole b)]
  | PARR(_,_) | QST(_,_) | WITH(_,_) | FORALL(_,_,_) -> 
    [NONE :: (get_subexp_from_monopole rule)]
  | EXISTS(str,i,b) -> get_subexp_prefix b
  | _ -> failwith "Unexpected term in a rule."

let rec greater_than_lst sub lst = 
  match lst with
  | [] -> true
  | SOME(s) :: lst1 when greater_than s sub -> greater_than_lst sub lst1
  | SOME(s) :: lst1 -> false

let rec cut_permutes_over cut rule = 
let rec get_subexp_cut cut = 
  match cut with 
  | EXISTS(_,_,body) -> 
    (match body with
    | TENSOR(a,b) ->       
      (match a,b with 
      | QST(CONS(sub2),b1), QST(CONS(sub4),b2) -> [NONE, SOME(sub2),
          NONE, SOME(sub4)]
      | BANG(CONS(sub1),QST(CONS(sub2),b1)), QST(CONS(sub4),b2) -> [SOME(sub1),
          SOME(sub2),NONE, SOME(sub4)]
      | QST(CONS(sub2),b1), BANG(CONS(sub3),QST(CONS(sub4),b2)) -> [NONE, SOME(sub2),
          SOME(sub3), SOME(sub4)]
      | BANG(CONS(sub1),QST(CONS(sub2),b1)), BANG(CONS(sub3),QST(CONS(sub4),b2)) ->
          [SOME(sub1), SOME(sub2), SOME(sub3), SOME(sub4)]
      | _ -> failwith "Wrong cut")
    | _ -> failwith "Wrong cut")
  | _ -> failwith "Wrong cut"
in let [a,SOME(b),c,SOME(d)] = get_subexp_cut cut in
let rule_prefix = get_subexp_prefix rule in 
let check_one_monopole mono_prefix =
  match a,c with 
  | SOME(a1), SOME(c1) ->
    ( match mono_prefix with
     | NONE :: rest -> true 
     | SOME(s) :: rest when (not (greater_than b s) && (not (weak b))) ||  
                            ((not (greater_than d s) && (not (weak d)))) -> true 
     | SOME(s) :: rest when (greater_than b s) && (greater_than c1 s) ->  
                              (greater_than_lst a1 rest)
    )
  | SOME(a1), NONE ->
    ( match mono_prefix with
     | NONE :: rest -> true
     | SOME(s) :: rest when (not (greater_than b s) && (not (weak b))) ||  
                            ((not (greater_than d s) && (not (weak d)))) -> true
     | SOME(s) :: rest when (greater_than d s) && (greater_than a1 s) -> true
    )
  | NONE, SOME(c1) -> 
    ( match mono_prefix with
     | NONE :: rest -> true
     | SOME(s) :: rest when (not (greater_than b s) && (not (weak b))) ||  
                            ((not (greater_than d s) && (not (weak d)))) -> true
     | SOME(s) :: rest when (greater_than b s) && (greater_than c1 s) -> true
    )
  | NONE, NONE -> 
    ( match mono_prefix with
     | NONE :: rest -> true
     | SOME(s) :: rest when (not (greater_than b s) && (not (weak b))) ||  
                            ((not (greater_than d s) && (not (weak d)))) -> true
     (*| SOME(s) :: rest -> true : It remains to check whether s is the least
element of the preorder.*)
    )
in 
let rec check_rules_monopoles rule_prefix =
  match rule_prefix with
  | [] -> true
  | mono :: lst -> (check_one_monopole mono) && check_rules_monopoles lst
in
check_rules_monopoles rule_prefix
    
(* The next auxiliary functions used to check the conditions of the Lemma 5.4 of the
paper above. *)

let rec has_bang rule = 
match rule with
  | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_)  -> false
  | TENSOR(b1, b2) | ADDOR(b1,b2) -> 
      has_bang b1 || has_bang b2
  | BANG(CONS(sub),b) -> true
  | EXISTS(str,i,b) ->  has_bang b
  | _ -> failwith "Unexpected term in a bipole."

let rec collect_quests rule = 
match rule with
  | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_)  -> []
  | TENSOR(b1, b2) | ADDOR(b1,b2) | PARR(b1,b2) | WITH(b1,b2) -> 
      List.append (collect_quests b1) (collect_quests b2)
  | BANG(CONS(sub),b) -> (collect_quests b)
  | EXISTS(_,_,b) | FORALL(_,_,b) ->  (collect_quests b)
  | QST(CONS(sub),b2) -> [sub]
  | _ -> failwith "Unexpected term in a rule."

let rec collect_bangs rule = 
match rule with
  | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_)  -> []
  | TENSOR(b1, b2) | ADDOR(b1,b2) | PARR(b1,b2) | WITH(b1,b2) -> 
      List.append (collect_bangs b1) (collect_bangs b2)
  | BANG(CONS(sub),b) -> [SOME(sub)]
  | EXISTS(_,_,b) | FORALL(_,_,b) ->  (collect_bangs b)
  | QST(CONS(sub),b2) -> []
  | _ -> failwith "Unexpected term in a rule."

let rec rule_permutes rule1 rule2 = 
(*Still need to check whether all subexponentials are unbounded.*)
if (not (has_bang rule1)) && (not (has_bang rule2)) then true else
let subRule1 = collect_bangs rule1 in
let subRule2 = collect_quests rule2 in
let rec greater_subexp sub1 sub2 = 
  match sub2 with
  | [] -> true 
  | head :: tail -> (greater_than_lst head sub1) && (greater_subexp sub1 tail)
in
greater_subexp subRule1 subRule2

(* Collects all the rules for which the cut rule does not permute. *)

let rec check_permutation cut rules = 
let rec not_permute cut rules = 
  match rules with
  | [] -> []
  | head :: tail when cut_permutes_over cut head -> not_permute cut tail
  | head :: tail -> head :: (not_permute cut tail)
in 
let rec permute_single_aux rule rules = 
match rules with
| [] -> true
| head :: tail -> (rule_permutes rule head) && permute_single_aux rule tail in
let rec permute_all_aux rules_not_permute rules =
match rules_not_permute with
| [] -> true
| head :: tail -> (permute_single_aux head rules) && (permute_all_aux tail rules) in
permute_all_aux (not_permute cut rules) rules

