open Term

(* Modified print functions to print to out channels other than the standart *)

let printf_comp_type out ct = match ct with
    | EQ -> Printf.fprintf out " = "
    | LESS -> Printf.fprintf out " < "
    | GEQ -> Printf.fprintf out " >= "
    | GRT -> Printf.fprintf out " > "
    | LEQ -> Printf.fprintf out " <= "
    | NEQ -> Printf.fprintf out " <> "

let printf_type_cls out ty = match ty with 
    | DEF -> Printf.fprintf out " DEF "
    | LOL -> Printf.fprintf out " LOL "

let rec printf_term out term = match term with 
  | VAR v -> 
		if v.tag = EIG then 
			(Printf.fprintf out "%s" v.str; Printf.fprintf out "EIG_"; Printf.fprintf out "%d" v.id) 
		else (Printf.fprintf out "%s" v.str; Printf.fprintf out "LOG_"; Printf.fprintf out "%d" v.id)
  | DB (i) -> Printf.fprintf out "_DB"; Printf.fprintf out "%d" i
  | INT (x) -> Printf.fprintf out "%d" x
  | CONS (x) -> Printf.fprintf out "%s" x
  | STRING (x) -> Printf.fprintf out "%s" x
  | APP (x, y) -> let n = List.length y in 
    let rec printf_app_lists out lst = 
    begin 
        match lst with
        | [] -> ()
        | t :: body -> printf_term out t; Printf.fprintf out ")"; printf_app_lists out body
    end in 
    for i = 1 to n do 
    Printf.fprintf out "("
    done; 
    printf_term out x; Printf.fprintf out " "; printf_app_lists out y
  | ABS (x, i, y) -> Printf.fprintf out "(/lam"; 
    Printf.fprintf out "%s" x; Printf.fprintf out "%d" i; 
    Printf.fprintf out " "; printf_term out y; Printf.fprintf out ")"
  | PLUS (ib1, ib2) -> printf_term out ib1; Printf.fprintf out " + "; printf_term out ib2
  | MINUS (ib1, ib2) -> printf_term out ib1; Printf.fprintf out " - "; printf_term out ib2
  | TIMES (ib1, ib2) -> printf_term out ib1; Printf.fprintf out " * "; printf_term out ib2
  | DIV (ib1, ib2) -> printf_term out ib1; Printf.fprintf out " / "; printf_term out ib2
  | SUSP (t, ol, nl, env) -> (*print_string "SUSP";*) 
    begin
      match t with 
      | DB i ->
        begin 
          match List.nth env (i-1) with 
          | Binding(t_bind, j) ->  printf_term out t_bind
          | _ -> printf_term out t
        end
      | _ -> printf_term out t
    end
  | PTR {contents = T t} ->  (*print_string "PTR";*)printf_term out t
  | PTR {contents = V v} ->  (*print_string "PTR";*)printf_term out (VAR v)
  | PRED (s, t, _) -> printf_term out t
  | EQU (s, i, t) -> Printf.fprintf out (" eq prop "); printf_term out t; Printf.fprintf out "%d" i
  | TOP -> Printf.fprintf out "top"
  | ONE -> Printf.fprintf out "one"
  | BOT -> Printf.fprintf out "bot"
  | ZERO -> Printf.fprintf out "zero"
  | NOT (t) -> Printf.fprintf out "not ("; printf_term out t; Printf.fprintf out ") "
  | COMP (c, i1, i2) -> printf_term out i1; printf_comp_type out c; printf_term out i2
  | ASGN ( i1, i2) -> printf_term out i1; Printf.fprintf out " is "; printf_term out i2
  | PRINT (t1) -> Printf.fprintf out "print "; printf_term out t1
  | CUT -> Printf.fprintf out "fail(cut)"
  | TENSOR (t1, t2) -> printf_term out t1; Printf.fprintf out " , "; printf_term out t2
  | ADDOR (t1, t2) -> printf_term out t1; Printf.fprintf out " ; "; printf_term out t2
  | PARR (t1, t2) -> printf_term out t1; Printf.fprintf out " | "; printf_term out t2
  | LOLLI (s, t1, t2) -> printf_term out t1; Printf.fprintf out (" ["); printf_term out s; Printf.fprintf out "] o- "; printf_term out t2
  | BANG (s, t) -> Printf.fprintf out " ["; printf_term out s; Printf.fprintf out "]! "; printf_term out t
  | HBANG (s, t) -> Printf.fprintf out " ["; printf_term out s; Printf.fprintf out "]^! "; printf_term out t
  | QST (s, t) -> Printf.fprintf out " ["; printf_term out s; Printf.fprintf out "]? "; printf_term out t
  | WITH (t1, t2) -> printf_term out t1; Printf.fprintf out " & "; printf_term out t2
  | FORALL (s, i, t) -> Printf.fprintf out "forall %s%d " s i; printf_term out t
  | EXISTS (s, i, t) -> Printf.fprintf out "exists %s%d " s i; printf_term out t
  | CLS (ty, t1, t2) -> printf_term out t1; printf_type_cls out ty; printf_term out t2
  | NEW (s, t) -> Printf.fprintf out "new/lam%s" s; printf_term out t
  | BRACKET (f) -> Printf.fprintf out "{ "; printf_term out f; Printf.fprintf out " }"

let rec printf_list_terms out args = 
   match args with
  | [] -> ()
  | term1 :: body -> printf_term out term1; Printf.fprintf out " || "; printf_list_terms out body

let rec printf_basic_type out btyp = match btyp with
	| TKIND (x) -> Printf.fprintf out "%s" x
	| TINT -> Printf.fprintf out "int"
	| TSTRING -> Printf.fprintf out "string"
	| TPRED -> Printf.fprintf out "o"
  | TSUBEX -> Printf.fprintf out "tsub"
	| TLIST (x) -> Printf.fprintf out "(list "; printf_basic_type out x; Printf.fprintf out ")"

let rec printf_type out typ = match typ with 
	| TBASIC (x) -> printf_basic_type out x
	| ARR (x,y) -> 
    match x with
      | TBASIC _ ->  printf_type out x; Printf.fprintf out " -> "; printf_type out y
      | _ -> Printf.fprintf out "("; 
        printf_type out x;Printf.fprintf out ")"; 
        Printf.fprintf out " -> "; printf_type out y

(* Printing to the standart output *)

let print_comp_type ct = printf_comp_type stdout ct ;;

let print_type_cls ty = printf_type_cls stdout ty ;;

let print_term term = printf_term stdout term ;;

let print_list_terms args = printf_list_terms stdout args ;;

let print_basic_type btyp = printf_basic_type stdout btyp ;;

let print_type typ = printf_type stdout typ ;;

(* Printing LaTeX code *)

let print_comp_type_tex out ct = match ct with
    | EQ -> Printf.fprintf out " = "
    | LESS -> Printf.fprintf out " < "
    | GEQ -> Printf.fprintf out " \\geq "
    | GRT -> Printf.fprintf out " > "
    | LEQ -> Printf.fprintf out " \\leq "
    | NEQ -> Printf.fprintf out " \\neq "

let print_type_cls_tex out ty = match ty with 
    | DEF -> Printf.fprintf out " DEF "
    | LOL -> Printf.fprintf out " LOL "

let rec print_term_tex out term = match term with 
  | VAR v -> 
		if v.tag = EIG then 
			(Printf.fprintf out "%s" v.str; Printf.fprintf out "EIG-"; Printf.fprintf out "%d" v.id) 
		else (Printf.fprintf out "%s" v.str; Printf.fprintf out "LOG-"; Printf.fprintf out "%d" v.id)
  | DB (i) -> Printf.fprintf out "-DB"; Printf.fprintf out "%d" i
  | INT (x) -> Printf.fprintf out "%d" x
  | CONS (x) -> Printf.fprintf out "%s" x
  | STRING (x) -> Printf.fprintf out "%s" x
  | APP (x, y) -> let n = List.length y in 
    let rec print_app_lists out lst = 
    begin 
        match lst with
        | [] -> ()
        | t :: body -> print_term_tex out t; Printf.fprintf out ")"; print_app_lists out body
    end in 
    for i = 1 to n do 
    Printf.fprintf out "("
    done; 
    print_term_tex out x; Printf.fprintf out " "; print_app_lists out y
  | ABS (x, i, y) -> Printf.fprintf out "(\\lambda "; 
    Printf.fprintf out "%s" x; Printf.fprintf out "%d" i; 
    Printf.fprintf out " "; print_term_tex out y; Printf.fprintf out ")"
  | PLUS (ib1, ib2) -> print_term_tex out ib1; Printf.fprintf out " + "; print_term_tex out ib2
  | MINUS (ib1, ib2) -> print_term_tex out ib1; Printf.fprintf out " - "; print_term_tex out ib2
  | TIMES (ib1, ib2) -> print_term_tex out ib1; Printf.fprintf out " * "; print_term_tex out ib2
  | DIV (ib1, ib2) -> print_term_tex out ib1; Printf.fprintf out " / "; print_term_tex out ib2
  | SUSP (t, ol, nl, env) -> (*print_string "SUSP";*) 
    begin
      match t with 
      | DB i ->
        begin 
          match List.nth env (i-1) with 
          | Binding(t_bind, j) ->  print_term_tex out t_bind
          | _ -> print_term_tex out t
        end
      | _ -> print_term_tex out t
    end
  | PTR {contents = T t} ->  (*print_string "PTR";*)print_term_tex out t
  | PTR {contents = V v} ->  (*print_string "PTR";*)print_term_tex out (VAR v)
  | PRED (s, t, _) -> print_term_tex out t
  | EQU (s, i, t) -> Printf.fprintf out (" eq prop "); print_term_tex out t; Printf.fprintf out "%d" i
  | TOP -> Printf.fprintf out "\\top"
  | ONE -> Printf.fprintf out "1"
  | BOT -> Printf.fprintf out "\\bot"
  | ZERO -> Printf.fprintf out "0"
  | NOT (t) -> Printf.fprintf out "\\neg "; print_term_tex out t;
  | COMP (c, i1, i2) -> print_term_tex out i1; print_comp_type_tex out c; print_term_tex out i2
  | ASGN ( i1, i2) -> print_term_tex out i1; Printf.fprintf out " is "; print_term_tex out i2
  | PRINT (t1) -> Printf.fprintf out "print "; print_term_tex out t1
  | CUT -> Printf.fprintf out "fail(cut)"
  | TENSOR (t1, t2) -> print_term_tex out t1; Printf.fprintf out " \\otimes "; print_term_tex out t2
  | ADDOR (t1, t2) -> print_term_tex out t1; Printf.fprintf out " \\oplus "; print_term_tex out t2
  | PARR (t1, t2) -> print_term_tex out t1; Printf.fprintf out " \\bindnasrepma "; print_term_tex out t2
  | LOLLI (s, t1, t2) -> print_term_tex out t2; Printf.fprintf out (" \\multimap_{"); print_term_tex out s; Printf.fprintf out "} "; print_term_tex out t1
  | BANG (s, t) -> Printf.fprintf out " !^{"; print_term_tex out s; Printf.fprintf out "} "; print_term_tex out t
  | HBANG (s, t) -> Printf.fprintf out " !^{\\hat{"; print_term_tex out s; Printf.fprintf out "}} "; print_term_tex out t
  | QST (s, t) -> Printf.fprintf out " ?^{"; print_term_tex out s; Printf.fprintf out "} "; print_term_tex out t
  | WITH (t1, t2) -> print_term_tex out t1; Printf.fprintf out " \\binampersand "; print_term_tex out t2
  | FORALL (s, i, t) -> Printf.fprintf out "\\forall %s%d " s i; print_term_tex out t
  | EXISTS (s, i, t) -> Printf.fprintf out "\\exists %s%d " s i; print_term_tex out t
  | CLS (ty, t1, t2) -> print_term_tex out t1; print_type_cls_tex out ty; print_term_tex out t2
  | NEW (s, t) -> Printf.fprintf out "new \\lambda %s" s; print_term_tex out t
  | BRACKET (f) -> Printf.fprintf out "\\{ "; print_term_tex out f; Printf.fprintf out " \\}"

let rec print_list_terms_tex out args = 
   match args with
  | [] -> ()
  | term1 :: body -> print_term_tex out term1; Printf.fprintf out " :: ";
    print_list_terms_tex out body

let rec print_basic_type_tex out btyp = match btyp with
	| TKIND (x) -> Printf.fprintf out "%s" x
	| TINT -> Printf.fprintf out "int"
	| TSTRING -> Printf.fprintf out "string"
	| TPRED -> Printf.fprintf out "o"
  | TSUBEX -> Printf.fprintf out "tsub"
	| TLIST (x) -> Printf.fprintf out "(list "; print_basic_type_tex out x; Printf.fprintf out ")"

let rec print_type_tex out typ = match typ with 
	| TBASIC (x) -> print_basic_type_tex out x
	| ARR (x,y) -> 
    match x with
      | TBASIC _ ->  print_type_tex out x; 
       Printf.fprintf out " \\rightarrow "; print_type_tex out y
      | _ -> Printf.fprintf out "("; print_type_tex out x;
       Printf.fprintf out ")"; Printf.fprintf out " \\rightarrow ";
       print_type_tex out y

(* Printing contexts *)

(* Removes special characters from a string *)
(* TODO: naive function. Fix it. *)
let remSpecial s = try match  (String.index s '$') with
  | n -> let cp = String.copy s in
    String.set cp n ' '; cp
  with Not_found -> s
;;

let ctxToTex (s, i) = 
  let news = remSpecial s in
  ("$\\Gamma_{"^news^"}^{"^(string_of_int i)^"}$")

let ctxToStr (s, i) = 
  let news = remSpecial s in
  ""^news^""^(string_of_int i)^""

let subexpTypeToStr tp = match tp with
  | LIN -> "lin"
  | UNB -> "unb"
  | REL -> "rel"
  | AFF -> "aff"

