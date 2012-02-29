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

let structRules : terms list ref = ref [] ;;
let cutRules : terms list ref = ref [] ;;
let introRules : terms list ref = ref [] ;;

let addStructRule r = 
  structRules := r :: !structRules

let addCutRule r = 
  cutRules := r :: !cutRules

let addIntroRule r = 
  introRules := r :: !introRules

(*Simple auxiliary functions that collects the subexponentials appearing in the
specification of rules. *)

let rec get_subexp_prefix rule =
(*Traverse a monopole and retrive a list of the form:
[a,b,c,d,...] containing the subexponential question marks appearing in the monopole.
*)
let rec get_subexp_from_monopole mono = 
  match mono with
  | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_) -> []
  | PARR(b1,b2) | WITH(b1,b2) -> 
    List.append (get_subexp_from_monopole b1) (get_subexp_from_monopole b2)
  | QST(CONS(sub),b2) -> [SOME(sub)]
  | FORALL(_,_,b) -> (get_subexp_from_monopole b)
  | _ -> failwith "Unexpected term in a monopole, while getting subexponentials
from monopole."
  in
(*This part adds to the output the bang that sourounds a monopole, if there is one.*)
  match rule with
  | NOT(_) | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_)  -> []
  | TENSOR(b1, b2) | ADDOR(b1,b2) -> 
      List.append (get_subexp_prefix b1) (get_subexp_prefix b2)
  | BANG(CONS(sub),b) -> [SOME(sub) :: (get_subexp_from_monopole b)]
  | PARR(_,_) | QST(_,_) | WITH(_,_) | FORALL(_,_,_) -> 
    [NONE :: (get_subexp_from_monopole rule)]
  | ABS(_, _, b) | EXISTS(_,_,b) -> get_subexp_prefix b
  | _ -> failwith "Unexpected term in a rule, while getting subexponentials
from bipoles."

(*Simple function that checks whether sub < s, for all s in lst.
let rec greater_than_lst_all sub lst = 
  match lst with
  | [] -> true
  | SOME(s) :: lst1 when greater_than sub s -> greater_than_lst_all sub lst1
  | SOME(s) :: lst1 -> false
*)

(* Relation among subexponentials. s1 >= s2 *)
let geq s1 s2 = greater_than s1 s2 || s1 = s2

(*Simple function that checks whether sub <= s, for all s in lst.*)
let rec less_than_lst_all sub lst = 
  match lst with
  | [] -> true
  | SOME(s) :: lst1 when geq s sub -> less_than_lst_all sub lst1
  | _ -> false


(*Simple function that checks whether sub <= s, for some s in lst.*)
let rec less_than_lst_one sub lst = 
  match lst with
  | [] -> false
  | SOME(s) :: lst1 when geq s sub  -> true
  | SOME(s) :: lst1 -> less_than_lst_one sub lst1

(*This function implements the conditions detailed in the paper for when a cut-rule
permutes over an introduction rule.*)

let rec cut_permutes_over cut rule = 
let rec get_subexp_cut cut = 
  match cut with 
  | ABS(_, _, body) | EXISTS(_,_,body) -> 
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
let subexp = keys subexTpTbl in
let check_one_monopole mono_prefix =
  match a,c with 
(*Case when the cut has two bangs.*)
  | SOME(a1), SOME(c1) ->
    ( match mono_prefix with
     | NONE :: rest -> (less_than_lst_all c1 rest) || (less_than_lst_all a1
rest)
     | SOME(s) :: rest when (not (geq b s) && (not (weak b))) ||  
                            ((not (geq d s) && (not (weak d)))) -> true 
     | SOME(s) :: rest when (geq a1 s) && (geq d s) ->  
                              (less_than_lst_all c1 rest)
     | SOME(s) :: rest when (geq b s) && (geq c1 s) ->  
                              (less_than_lst_all a1 rest)
     | _ -> false
    )
(*Cases when the cut has a single bang.*)
  | SOME(a1), NONE ->
    ( match mono_prefix with
     | NONE :: rest -> true
     | SOME(s) :: rest when (not (geq b s) && (not (weak b))) ||  
                            ((not (geq d s) && (not (weak d)))) -> true
     | SOME(s) :: rest when (geq d s) && (geq a1 s) -> true
     | _ -> false
    )
  | NONE, SOME(c1) -> 
    ( match mono_prefix with
     | NONE :: rest -> true
     | SOME(s) :: rest when (not (geq b s) && (not (weak b))) ||  
                            ((not (geq d s) && (not (weak d)))) -> true
     | SOME(s) :: rest when (geq b s) && (geq c1 s) -> true
     | _ -> false
    )
(*Case when the cut has no bangs.*)
  | NONE, NONE -> 
    ( match mono_prefix with
     | NONE :: rest -> true
     | SOME(s) :: rest when (not (geq b s) && (not (weak b))) ||  
                            ((not (geq d s) && (not (weak d)))) -> true
     | SOME(s) :: rest -> 
        Hashtbl.fold (fun key data acc -> if (geq key s) then acc
        else false) subexTpTbl true 
    )
in 
let rec check_rules_monopoles rule_prefix =
  match rule_prefix with
  | [] -> true
  | mono :: lst -> (check_one_monopole mono) && check_rules_monopoles lst
in
check_rules_monopoles rule_prefix
    
(* The next auxiliary functions used to check the conditions of the Lemma 5.4 of the
paper mentioned above. *)

let rec has_bang rule = 
match rule with
  | NOT(_) | PRED(_,_,_) | ONE | BOT | ZERO | TOP 
  | EQU(_,_,_) | QST(_,_) | PARR(_,_) -> false
  | TENSOR(b1, b2) | ADDOR(b1,b2) -> 
      has_bang b1 || has_bang b2
  | BANG(CONS(sub),b) -> true
  | ABS(_, _, b) | EXISTS(_,_,b) ->  has_bang b
  | _ -> failwith "Unexpected term in a bipole, while checking whether there is a bang."

let rec collect_quests rule = 
match rule with
  | NOT(_) | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_)  -> []
  | TENSOR(b1, b2) | ADDOR(b1,b2) | PARR(b1,b2) | WITH(b1,b2) -> 
      List.append (collect_quests b1) (collect_quests b2)
  | BANG(CONS(sub),b) -> (collect_quests b)
  | ABS(_, _, b) | EXISTS(_,_,b) | FORALL(_,_,b) ->  (collect_quests b)
  | QST(CONS(sub),b2) -> [SOME(sub)]
  | _ -> failwith "Unexpected term in a rule, while collecting quests."

let rec collect_bangs rule = 
match rule with
  | NOT(_) | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_)  -> []
  | TENSOR(b1, b2) | ADDOR(b1,b2) | PARR(b1,b2) | WITH(b1,b2) -> 
      List.append (collect_bangs b1) (collect_bangs b2)
  | BANG(CONS(sub),b) -> [SOME(sub)]
  | ABS(_, _, b) | EXISTS(_,_,b) | FORALL(_,_,b) ->  (collect_bangs b)
  | QST(CONS(sub),b2) -> []
  | _ -> failwith "Unexpected term in a rule, while collecting bangs."


let rec findEquiv rule structRules = 
let rec findHead rule = 
match rule with 
| NOT(PRED(_,b,_)) -> b
| ABS(_, _, b) | EXISTS(_,_,b) -> findHead b
| TENSOR(b1, b2) -> findHead b1
| _ -> failwith "Unexpected term in a rule, while extracting the head."
in
let rec findQST rule = 
match rule with 
| QST(CONS(sub),_) -> sub
| ABS(_, _, b) | EXISTS(_,_,b) -> findQST b
| TENSOR(b1, b2) -> findQST b2
| _ -> failwith "Unexpected term in a rule, while extracting the QST."
in let hdRule = findHead rule in
let rec findEquiv_Aux rules = 
match rules with 
| [] -> []
| rl :: tail -> 
  let hdStruct = findHead rl in
  if eq hdRule hdStruct then SOME(findQST rl) :: (findEquiv_Aux tail) 
    else (findEquiv_Aux tail)
in
findEquiv_Aux structRules  


let rec rule_permutes rule1 rule2 strRules = 
let rec condition_equiv sub bangs equiv = 
  match bangs with
  | [] -> true
  | SOME(s) :: lst when  (geq sub s) || (less_than_lst_one s equiv)
      -> condition_equiv sub lst equiv
  | SOME(s) :: lst -> false
in
let rec greater_subexp bangs quests equiv = 
  (match quests with
  | [] -> true 
  | SOME(sub) :: lst when (condition_equiv sub bangs equiv)
  (* Check whether there is an equivalence or the body is ok.*)
      -> (greater_subexp bangs lst equiv)
  | _ -> false)
in
(* Checking that all subexponentials are unbounded *)
match Hashtbl.fold (fun key data acc -> if key = "$gamma" then acc else
                      (data = UNB) & acc) subexTpTbl true 
with
| true -> 
  (match (has_bang rule2) with
   | false ->
      (match (has_bang rule1) with
       | false -> true (* If no rule has a bang, then ok*)
       | true -> 
          let rule1Bang = collect_bangs rule1 in
          let rule2Quest = collect_quests rule2 in
          let equiv = findEquiv rule2 strRules in
            greater_subexp rule1Bang rule2Quest equiv
      )
   | true ->
       (match (has_bang rule1) with
       | false -> false (* If no rule has a bang, then ok*)
       | true ->       
          let rule1Bang = collect_bangs rule1 in 
          let rule2Bang = collect_bangs rule2 in
          (match rule1Bang with
            | SOME(s) :: lst -> 
                let all_bangs = List.append lst rule2Bang in
                List.fold_left (fun acc (SOME(s1)) -> (s1 = s) & acc) true all_bangs
          )
        )
  )
| false -> false (*There is some bounded subexponential.*)

let print_rule rule = print_endline (Prints.termToString rule)

(* Collects all the rules for which the cut rule do not permute and then checks
whether all rules permute over these rules. *)
let rec check_permutation cut rules strRules = 
let rec not_permute cut rules = 
  match rules with
  | [] -> []
  | head :: tail when cut_permutes_over cut head -> not_permute cut tail
  | head :: tail -> head :: (not_permute cut tail)
in 
let rec permute_single_aux rule rules = 
  match rules with
  | [] -> true
  | head :: tail -> (rule_permutes rule head strRules) && (permute_single_aux rule
  tail) in
let rec permute_all_aux rules_not_permute rules =
  match rules_not_permute with
  | [] -> true
  | head :: tail -> (permute_single_aux head rules) && (permute_all_aux tail rules) in
let rulesCutNotPermute = not_permute cut rules in 
  print_endline "The cut rule does not permute over the following rules:";
  List.iter print_rule rulesCutNotPermute;
  permute_all_aux rulesCutNotPermute rules


let rec cut_principal () = 
let rec cut_principal_aux cuts = 
  match cuts with
  | [] -> true
  | cut :: lst when check_permutation cut !introRules !structRules -> 
        cut_principal_aux lst 
  | _ -> false
in 
cut_principal_aux !cutRules

(* Some testing functions.*)

let rec test1 () = 
    match !cutRules with
    | [] -> ()
    | cutHd :: cutTail -> 
      List.iter (fun ele -> 
        if (cut_permutes_over cutHd ele) then print_endline "Cut permutes."      
        else print_endline "Cut does not permute.") !introRules

let rec test2 () = 
    match !introRules with
    | [] -> print_endline "Should not come here!"
    | rule1 :: rule2 :: lst -> 
      if rule_permutes rule1 rule2 !structRules then 
        print_endline "Rule permutes." else print_endline "Rule does not permute."

let rec test3 () = 
    match !introRules with
    | [] -> print_endline "Should not come here!"
    | rule1 :: lst -> let equiv = findEquiv rule1 !structRules in 
        List.iter (fun (SOME(s)) -> print_endline s) equiv;
        print_endline "Found equivalences"


