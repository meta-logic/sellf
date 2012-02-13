(*
 * Some common functions used for every type of proof search.
 * E.g.: in the files interpreter, macro and blindsearch
 *)

open Basic
open Structs
open ProofTree
open Term
open Prints

(* Incremented when solving the first branch of a tensor. Decremented when
solving the second branch of a tensor. *)
let flagTensor = ref 0 ;;

(* Set to true when a top is found, set to false when an additive binary rule is
applied (only & on our case). *)
let flagTop = ref false ;;

let unify = 
  let module Unify = 
    Unify.Make ( struct
      let instantiatable = Term.LOG
      let constant_like = Term.EIG
    end )
  in Unify.pattern_unify

(* TODO: put this in terms? *)
(* Function to substitute a variable in a formula *)
let rec apply_ptr f = match f with
  | ABS(s, i, t) ->
      varid := !varid + 1;
      let newVar = V {str = s; id = !varid; tag = Term.LOG; ts = 0; lts = 0} in
      let ptr = PTR {contents = newVar} in
      let newf = Norm.hnorm (APP(ABS(s, i, t), [ptr])) in
      apply_ptr newf
  | x -> x

let unifies f1 f2 =
  let fp1 = apply_ptr f1 in
  let fp2 = apply_ptr f2 in
    if !verbose then begin
      print_string "****** Unifying (head of first with second): \n"; 
      print_term fp1; print_newline (); print_term fp2;
      print_newline ();
    end;
    match fp1, fp2 with
    | LOLLI(CONS(s), head, body), (PRED (str2, terms2, _)) -> 
      begin match head with
      | (PRED(str1, terms1, _)) ->
        begin try match unify terms1 terms2 with
          | () ->
	    if !verbose then begin
              print_string "******* After unification: \n"; print_term fp1; print_newline ();
              print_term fp2; print_newline ()
	    end;
            (fp1, fp2)
          with _ ->  failwith "Unification not possible."
        end
      | _ -> failwith "Head of a clause not a predicate."
      end
    | _ -> failwith "Formulas not compatible (should be lolli and pred)."
;;

(**************** SIDE CONDITIONS OF RULES **********************)

(* Checks if bang rule can be applied with subexponential s *)
let condition_bang s = 
  let subsempt = empty_bang s in
  let rec all_empty subs = match subs with
    | [] -> true
    | h::t -> match get_forms h with
      | [] -> all_empty t
      | _ -> 
        if !verbose then 
          print_string ("Failed in bang rule with subexponential: "^s^"\n"); 
	      false
  in all_empty subsempt
;;

(* NOTE: this can be optimized as follows: get all non weakenable formulas, if
it contains something, check if it is unifiable, if its empty, check the
classical contexts *)
(* TODO: implement a smarter unification function that returns true if the terms
are the same and an error or exception if they are not unifiable. *)
let condition_init f = 
  let rec init_aux f lst = match lst with
    | [] -> false
    | (s, f1) :: tl -> begin
      match (f, f1) with
        | (PRED(str, t, p), PRED(str1, t1, p1)) when str = str1 -> begin
          try match unify t t1 with
            | () -> 
              let rest = not_weakenable () in
              if !flagTensor > 0 || !flagTop || rest = [] || rest = [f1] then true
              else init_aux f tl
            with _ -> init_aux f tl
          end
        | (NOT(PRED(str, t, p)), NOT(PRED(str1, t1, p1))) when str = str1 -> begin
          try match unify t t1 with
            | () ->
              let rest = not_weakenable () in
              if !flagTensor > 0 || !flagTop || rest = [] || rest = [f1] then true
              else init_aux f tl
            with _ -> init_aux f tl
          end
        | (_, _) -> init_aux f tl
    end
  in
  init_aux f (to_pairs !context)


(* Solves negation of formulas by applying DeMorgan rules until atomic level *)
let rec deMorgan f = match f with
  | NOT(t) -> begin 
    match t with
      | NOT(t1) -> t1
      | PRED(str, terms, p) -> NOT(t) 
      | TENSOR(f1, f2) -> PARR(deMorgan (NOT(f1)), deMorgan (NOT(f2)))
      | PARR(f1, f2) -> TENSOR(deMorgan (NOT(f1)), deMorgan (NOT(f2)))
      | WITH(f1, f2) -> ADDOR(deMorgan (NOT(f1)), deMorgan (NOT(f2)))
      | ADDOR(f1, f2) -> WITH(deMorgan (NOT(f1)), deMorgan (NOT(f2)))
      | EXISTS(s, i, f1) -> FORALL(s, i, deMorgan (NOT(f1)))
      | FORALL(s, i, f1) -> EXISTS(s, i, deMorgan (NOT(f1)))
      | QST(s, f1) -> BANG(s, deMorgan (NOT(f1)))
      | BANG(s, f1) -> QST(s, deMorgan (NOT(f1)))
      | LOLLI(s, f1, f2) -> TENSOR((QST(s, f2)), deMorgan (NOT(f1)))
      | TOP -> ZERO
      | ZERO -> TOP
      | BOT -> ONE
      | ONE -> BOT
      | COMP(ct, t1, t2) -> begin
        match ct with
          | EQ -> COMP(NEQ, t1, t2)
          | NEQ -> COMP(EQ, t1, t2)
          | LESS -> COMP(GEQ, t1, t2)
          | GEQ -> COMP(LESS, t1, t2)
          | GRT -> COMP(LEQ, t1, t2)
          | LEQ -> COMP(GRT, t1, t2)
        end
      | _ -> print_term f; failwith "Error while applying deMorgan to term."
    end
  | t -> t (* Non-negated term *)

(* Solves an arithmetic expression *)
let rec solve_exp e = match e with
  | INT (x) -> x
  | VAR v -> 1(* Infer the variable value?? *)
  | PLUS (x, y) -> (solve_exp x) + (solve_exp y)
  | MINUS (x, y) -> (solve_exp x) - (solve_exp y)
  | TIMES (x, y) -> (solve_exp x) * (solve_exp y)
  | DIV (x, y) -> (solve_exp x) / (solve_exp y)
  | PTR {contents = T t} -> solve_exp t
  | PTR {contents = V t} when t.tag = Term.LOG -> 
      print_string "ERROR: Cannot handle comparisons with logical variables.";  
      print_term e; 
      print_newline (); 
      0
  | bla -> print_string "[ERROR] Unexpected term in a comparison: "; print_term bla; print_newline (); 0
;;

(* Solves an arithmetic comparison *)
let solve_cmp c e1 e2 = 
  let n1 = solve_exp e1 in 
  let n2 = solve_exp e2 in
    match c with
      | EQ -> n1 = n2
      | LESS -> n1 < n2
      | GEQ -> n1 >= n2        
      | GRT -> n1 > n2
      | LEQ -> n1 <= n2
      | NEQ -> n1 != n2
;;

(*Solves assignment *)
let solve_asgn e1 e2 = 
  if !verbose then begin
    print_string "****** Unifying (head of first with second): \n"; 
    print_term e1; print_newline (); print_term e2;
    print_newline ()
  end;
  let n2 = solve_exp e2 in
  try 
    unify e1 (INT(n2)); 
    if !verbose then begin
      print_string "******* After unification: \n"; 
      print_term e1; print_newline (); print_int n2; 
      print_newline ()
    end;
    true
  with 
  | _ -> if !verbose then print_endline "Failed to assign a variable to an int in an assigment."; false;;


