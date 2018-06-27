(*
This module implements the static conditions detailed in Section 5 of the paper
below for determining whether an object rule permutes over aanother object rule.
This analysis is necessary for determining whether an object-logic proof with cuts
can be transformed into a proof with principal cuts only.

"Extended Framework for Specifying and Reasoning about Proof Systems
by Vivek Nigam, Elaine Pimentel, and Giselle Reis"

*)
open Basic
open Types
open Specification

let unify = 
  let module Unify = 
    Unify.Make ( struct
      let instantiatable = LOG
      let constant_like = EIG
    end )
  in Unify.pattern_unify
;;

(* Assuming that the cut has the following shape:

    exists A. !a ?b lft{A} tensor !c ?d right{A}
*)

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
  | QST(CONST(sub),b2) -> [Some(sub)]
  | FORALL(_,_,b) -> (get_subexp_from_monopole b)
  | _ -> failwith "Unexpected term in a monopole, while getting subexponentials
from monopole."
  in
(*This part adds to the output the bang that sourounds a monopole, if there is one.*)
  match rule with
  | NOT(_) | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_)  -> []
  | TENSOR(b1, b2) | ADDOR(b1,b2) -> 
      List.append (get_subexp_prefix b1) (get_subexp_prefix b2)
  | BANG(CONST(sub),b) -> [Some(sub) :: (get_subexp_from_monopole b)]
  | PARR(_,_) | QST(_,_) | WITH(_,_) | FORALL(_,_,_) -> 
    [None :: (get_subexp_from_monopole rule)]
  | ABS(_, _, b) | EXISTS(_,_,b) -> get_subexp_prefix b
  | _ -> failwith "Unexpected term in a rule, while getting subexponentials
from bipoles."

(*Simple function that checks whether sub < s, for all s in lst.
let rec greater_than_lst_all sub lst = 
  match lst with
  | [] -> true
  | Some(s) :: lst1 when greater_than sub s -> greater_than_lst_all sub lst1
  | Some(s) :: lst1 -> false
*)

(* Relation among subexponentials. s1 >= s2 *)
let geq s1 s2 = Subexponentials.greater_than s1 s2 || s1 = s2

(*Simple function that checks whether sub <= s, for all s in lst.*)
let rec less_than_lst_all sub lst = 
  match lst with
  | [] -> true
  | Some(s) :: lst1 when geq s sub -> less_than_lst_all sub lst1
  | _ -> false


(*Simple function that checks whether sub <= s, for Some s in lst.*)
let rec less_than_lst_one sub lst = 
  match lst with
  | [] -> false
  | Some(s) :: lst1 when geq s sub  -> true
  | Some(s) :: lst1 -> less_than_lst_one sub lst1
  | _ -> failwith "Unexpected case in less_than_lst_one function."

(* This function gets the subexponentials of a cut. 
It returns the subexponentials in the following form:
!a?b lft{A} tensor !c?d rght{B}
 *)

let rec get_subexp_cut cut = 
  match cut with 
  | ABS(_, _, body) | EXISTS(_,_,body) -> 
    (match body with
    | TENSOR(a,b) ->       
      (match a,b with 
      | QST(CONST(sub2),PRED("lft",_ , _)), QST(CONST(sub4),PRED("rght", _, _)) -> 
          [None, Some(sub2), None, Some(sub4)]
      | QST(CONST(sub2),PRED("mlft",_ , _)), QST(CONST(sub4),PRED("mrght", _, _)) -> 
          [None, Some(sub2), None, Some(sub4)]
      | QST(CONST(sub4),PRED("rght", _, _)), QST(CONST(sub2),PRED("lft",_, _))  -> 
          [None, Some(sub2), None, Some(sub4)]
      | QST(CONST(sub4),PRED("mrght", _, _)), QST(CONST(sub2),PRED("mlft",_, _))  -> 
          [None, Some(sub2), None, Some(sub4)]
      | BANG(CONST(sub1),QST(CONST(sub2),PRED("lft",_, _))), QST(CONST(sub4),PRED("rght", _, _)) -> 
          [Some(sub1), Some(sub2),None, Some(sub4)]
      | BANG(CONST(sub1),QST(CONST(sub2),PRED("mlft",_, _))), QST(CONST(sub4),PRED("mrght", _, _)) -> 
          [Some(sub1), Some(sub2),None, Some(sub4)]
      | QST(CONST(sub4),PRED("rght", _, _)), BANG(CONST(sub1),QST(CONST(sub2),PRED("lft",_, _))) -> 
          [Some(sub1), Some(sub2),None, Some(sub4)]
      | QST(CONST(sub4),PRED("mrght", _, _)), BANG(CONST(sub1),QST(CONST(sub2),PRED("mlft",_, _))) -> 
          [Some(sub1), Some(sub2),None, Some(sub4)]
      | QST(CONST(sub2),PRED("lft",_, _)), BANG(CONST(sub3),QST(CONST(sub4),PRED("rght", _, _))) -> 
          [None, Some(sub2), Some(sub3), Some(sub4)]
      | QST(CONST(sub2),PRED("mlft",_, _)), BANG(CONST(sub3),QST(CONST(sub4),PRED("mrght", _, _))) -> 
          [None, Some(sub2), Some(sub3), Some(sub4)]
      | BANG(CONST(sub3),QST(CONST(sub4),PRED("rght", _, _))), QST(CONST(sub2),PRED("lft",_, _)) -> 
          [None, Some(sub2), Some(sub3), Some(sub4)]
      | BANG(CONST(sub3),QST(CONST(sub4),PRED("mrght", _, _))), QST(CONST(sub2),PRED("mlft",_, _)) -> 
          [None, Some(sub2), Some(sub3), Some(sub4)]
      | BANG(CONST(sub1),QST(CONST(sub2),PRED("lft",_, _))), BANG(CONST(sub3),QST(CONST(sub4),PRED("rght", _, _))) ->
          [Some(sub1), Some(sub2), Some(sub3), Some(sub4)]
      | BANG(CONST(sub1),QST(CONST(sub2),PRED("mlft",_, _))), BANG(CONST(sub3),QST(CONST(sub4),PRED("mrght", _, _))) ->
          [Some(sub1), Some(sub2), Some(sub3), Some(sub4)]
      | BANG(CONST(sub3),QST(CONST(sub4),PRED("rght", _, _))), BANG(CONST(sub1),QST(CONST(sub2),PRED("lft",_, _))) ->
          [Some(sub1), Some(sub2), Some(sub3), Some(sub4)]
      | BANG(CONST(sub3),QST(CONST(sub4),PRED("mrght", _, _))), BANG(CONST(sub1),QST(CONST(sub2),PRED("mlft",_, _))) ->
          [Some(sub1), Some(sub2), Some(sub3), Some(sub4)]
      | _ -> failwith "Wrong cut")
    | _ -> failwith "Wrong cut")
  | _ -> failwith "Wrong cut"


(*This function implements the conditions detailed in the paper for when a cut-rule
permutes over an introduction rule.*)

let rec cut_permutes_over cut rule = 
let [a,Some(b),c,Some(d)] = get_subexp_cut cut in
let rule_prefix = get_subexp_prefix rule in 
let check_one_monopole mono_prefix =
  match a,c with 
(*Case when the cut has two bangs.*)
  | Some(a1), Some(c1) ->
    ( match mono_prefix with
     | None :: rest -> (less_than_lst_all c1 rest) && (less_than_lst_all a1
rest)
     | Some(s) :: rest when (not (geq b s) && (not (Subexponentials.weak b))) &&  
                            ((not (geq d s) && (not (Subexponentials.weak d)))) -> true 
     | Some(s) :: rest when (geq a1 s) && (geq d s) ->  
                              (less_than_lst_all c1 rest)
     | Some(s) :: rest when (geq b s) && (geq c1 s) ->  
                              (less_than_lst_all a1 rest)
     | _ -> false
    )
(*Cases when the cut has a single bang.*)
  | Some(a1), None ->
    ( match mono_prefix with
     | None :: rest -> true
     | Some(s) :: rest when (not (geq b s) && (not (Subexponentials.weak b))) &&  
                            ((not (geq d s) && (not (Subexponentials.weak d)))) -> true
     | Some(s) :: rest when (geq d s) && (geq a1 s) -> true
     | _ -> false
    )
  | None, Some(c1) -> 
    ( match mono_prefix with
     | None :: rest -> true
     | Some(s) :: rest when (not (geq b s) && (not (Subexponentials.weak b))) &&  
                            ((not (geq d s) && (not (Subexponentials.weak d)))) -> true
     | Some(s) :: rest when (geq b s) && (geq c1 s) -> true
     | _ -> false
    )
(*Case when the cut has no bangs.*)
  | None, None -> 
    ( match mono_prefix with
     | None :: rest -> true
     | Some(s) :: rest when (not (geq b s) && (not (Subexponentials.weak b))) &&  
                            ((not (geq d s) && (not (Subexponentials.weak d)))) -> true
     | Some(s) :: rest -> 
        Hashtbl.fold (fun key data acc -> if (geq key s) then acc
        else false) Subexponentials.typeTbl true
     | _ -> failwith "Unexpected case when cut has no bangs."
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
  | EQU(_,_,_) | QST(_,_) | PARR(_,_) | FORALL(_,_,_) -> false
  | TENSOR(b1, b2) | ADDOR(b1,b2) -> 
      has_bang b1 || has_bang b2
  | BANG(CONST(sub),b) -> true
  | ABS(_, _, b) | EXISTS(_,_,b) ->  has_bang b
  | _ -> failwith "Unexpected term in a bipole, while checking whether there is a bang."

let rec collect_quests rule = 
match rule with
  | NOT(_) | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_)  -> []
  | TENSOR(b1, b2) | ADDOR(b1,b2) | PARR(b1,b2) | WITH(b1,b2) -> 
      List.append (collect_quests b1) (collect_quests b2)
  | BANG(CONST(sub),b) -> (collect_quests b)
  | ABS(_, _, b) | EXISTS(_,_,b) | FORALL(_,_,b) ->  (collect_quests b)
  | QST(CONST(sub),b2) -> [Some(sub)]
  | _ -> failwith "Unexpected term in a rule, while collecting quests."

let rec collect_bangs rule = 
match rule with
  | NOT(_) | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_)  -> []
  | TENSOR(b1, b2) | ADDOR(b1,b2) | PARR(b1,b2) | WITH(b1,b2) -> 
      List.append (collect_bangs b1) (collect_bangs b2)
  | BANG(CONST(sub),b) -> [Some(sub)]
  | ABS(_, _, b) | EXISTS(_,_,b) | FORALL(_,_,b) ->  (collect_bangs b)
  | QST(CONST(sub),b2) -> []
  | _ -> failwith "Unexpected term in a rule, while collecting bangs."


let rec findHead rule = 
match rule with 
| NOT(PRED(_,b,_)) -> b
| ABS(s, i, b) -> 
      Term.varid := !Term.varid + 1;
      let new_var = V ({str = s; id = !Term.varid; tag = LOG; ts = 0; lts = 0}) in
      let ptr = PTR {contents = new_var} in
      let newf = Norm.hnorm (APP (rule, [ptr])) in
        findHead newf
| EXISTS(s,i,b) ->
      Term.varid := !Term.varid + 1;
      let new_var = V ({str = s; id = !Term.varid; tag = LOG; ts = 0; lts = 0}) in
      let ptr = PTR {contents = new_var} in
      let newf = Norm.hnorm (APP (ABS (s, 1, b), [ptr])) in
        findHead newf
| TENSOR(b1, b2) -> findHead b1
| _ -> failwith "Unexpected term in a rule, while extracting the head."


let rec findEquiv rule structRules = 
let rec findQST rule = 
match rule with 
| QST(CONST(sub),_) -> sub
| ABS(_, _, b) | EXISTS(_,_,b) -> findQST b
| TENSOR(b1, b2) -> findQST b2
| _ -> failwith "Unexpected term in a rule, while extracting the QST."
in let hdRule = findHead rule in
let rec findEquiv_Aux rules = 
match rules with 
| [] -> []
| rl :: tail -> 
  let hdStruct = findHead rl in
  begin
    try match unify hdRule hdStruct with
    | () -> Some(findQST rl) :: (findEquiv_Aux tail) 
    with _ -> findEquiv_Aux tail
  end
in
findEquiv_Aux structRules  


let rec rule_permutes rule1 rule2 strRules = 
let rec condition_equiv sub bangs equiv = 
  match bangs with
  | [] -> true
  | Some(s) :: lst when  (geq sub s) || (less_than_lst_one s equiv)
      -> condition_equiv sub lst equiv
  | Some(s) :: lst -> false
  | _ -> failwith "Unexpected case."
in
let rec greater_subexp bangs quests equiv = 
  (match quests with
  | [] -> true 
  | Some(sub) :: lst when (condition_equiv sub bangs equiv)
  (* Check whether there is an equivalence or the body is ok.*)
      -> (greater_subexp bangs lst equiv)
  | _ -> false)
in
(* Checking that all subexponentials are unbounded *)
match Hashtbl.fold (fun key data acc -> if key = "gamma" then acc else
                      (data = Subexponentials.UNB) & acc) Subexponentials.typeTbl true 
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
            | Some(s) :: lst -> 
                let all_bangs = List.append lst rule2Bang in
                List.fold_left (fun acc (Some(s1)) -> (s1 = s) & acc) true all_bangs
            | _ -> failwith "Unexpected case."
          )
        )
  )
| false -> false (*There is some bounded subexponential.*)

let termsListToString args = List.fold_right (fun el acc ->
  (Prints.termToString el)^" "^acc) args ""


(* Function to pretty print a rule according to its head. *)
let rec print_rule rule = 
let rec replace_Log term = 
  match term with
  | VAR _ -> CONST("_")
  | PTR _ -> CONST("_")
  | APP(b1, lb2) ->  
      let t1 = replace_Log b1 in
      let lt1 = List.map (fun ele -> replace_Log ele) lb2 in 
        APP(t1, lt1)  
  | t -> t
in 
let rec pretty_print hd = 
  match hd with
  | APP(CONST("lft"), b) -> 
    let _ = print_string "Left Introduction rule for " in
    print_string (termsListToString b)
  | APP(CONST("mlft"), b) -> 
    let _ = print_string "Left Introduction rule for " in
    print_string (termsListToString b)
  | APP(CONST("rght"), b) -> 
    let _ = print_string "Right Introduction rule for " in
    print_string (termsListToString b)
  | APP(CONST("mrght"), b) -> 
    let _ = print_string "Right Introduction rule for " in
    print_string (termsListToString b)
  | _ -> failwith "Unexpected term while printing the head of the rule."
in 
let hd = replace_Log (findHead rule) in
pretty_print hd

let print_rule_endline rule = print_rule rule; print_endline ""

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
  | head :: tail -> 
    let p1 = rule_permutes rule head strRules in
    let p2 = permute_single_aux rule tail in
    if not p1 then print_rule_endline head;  
    p1 && p2
in
let rec permute_all_aux rules_not_permute rules =
  match rules_not_permute with
  | [] -> true
  | head :: tail -> 
    print_string "\nThe "; 
    print_rule head; 
    print_endline " does not permute with:";
    let b1 = (permute_single_aux head rules) in
    let b2 = (permute_all_aux tail rules) in
    b1 && b2
in
let rulesCutNotPermute = not_permute cut rules in
  if List.length rulesCutNotPermute > 0 then
    (print_endline "\nThe cut rule does not permute over the following rules:";
    List.iter (fun ele -> print_rule ele; print_endline "") rulesCutNotPermute;
    permute_all_aux rulesCutNotPermute rules)
  else 
    (print_endline "\nThe cut rule permutes over all rules."; true)
    
(* This function check whether a list of rules contains only bipoles *)
let rec areBipoles rules = match rules with 
| [] -> true
| rl :: lst when Term.isBipole rl -> areBipoles lst
| rl :: lst -> 
    print_endline ("The following clause is NOT a bipole -> \n"^Prints.termToString rl); 
    false

let rec cut_principal spec = 
let rec cut_principal_aux cuts = 
  match cuts with
  | [] -> true
  | cut :: lst when check_permutation cut (Specification.getIntroRules spec) (Specification.getStructRules spec) -> 
        cut_principal_aux lst 
  | _ -> false
in 
if areBipoles (Specification.getIntroRules spec) then 
  cut_principal_aux (Specification.getCutRules spec)
else false

let rec weak_coherent spec =
let rec collect_quests_aux rule str = 
match rule with
  | NOT(_) | PRED(_,_,_) | ONE | BOT | ZERO | TOP | EQU(_,_,_)  -> []
  | TENSOR(b1, b2) | ADDOR(b1,b2) | PARR(b1,b2) | WITH(b1,b2) -> 
      List.append (collect_quests_aux b1 str) (collect_quests_aux b2 str)
  | BANG(CONST(sub),b) -> (collect_quests_aux b str)
  | ABS(_, _, b) | EXISTS(_,_,b) | FORALL(_,_,b) ->  (collect_quests_aux b str)
  | QST(CONST(sub),PRED(str1,_,_)) when str = str1 -> [Some(sub)]
  | QST(CONST(sub),_) -> []
  | _ -> failwith "Unexpected term in a rule, while collecting string quests."
in
let all_subs_lft = 
  List.fold_left (fun acc ele -> 
    List.append ( (collect_quests_aux ele "lft") @ (collect_quests_aux ele "mlft") ) acc) [] (Specification.getIntroRules spec)
in
let all_subs_rght = 
  List.fold_left (fun acc ele -> 
    List.append ( (collect_quests_aux ele "rght") @ (collect_quests_aux ele "mrght") ) acc) [] (Specification.getIntroRules spec)
in
let check_lft_subs b lft_subs = 
  List.fold_left (fun acc (Some(s)) -> 
    if geq s b then acc else false) true lft_subs
in
let check_rght_subs d rght_subs = 
  List.fold_left (fun acc (Some(t)) -> 
    if geq t d then acc else false) true rght_subs
in
let rec weak_cut_aux cut = 
  let [a,Some(b),c,Some(d)] = get_subexp_cut cut in
  (check_lft_subs b all_subs_lft) &&  (check_rght_subs d all_subs_rght)
in
let rec weak_cut_aux_lst cuts =      
match cuts with
| [] -> true
| cut :: lst when weak_cut_aux cut ->
        weak_cut_aux_lst lst 
| _ -> false
in
if areBipoles (Specification.getIntroRules spec) then 
  weak_cut_aux_lst (Specification.getCutRules spec)
else false

(* Some testing functions, for debugging only.*)

(*
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
        List.iter (fun (Some(s)) -> print_endline s) equiv;
        print_endline "Found equivalences"
*)


