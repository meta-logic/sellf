
(* Giselle Machado Reis - 2012 *)

open Term

(* Functions to transform formulas to string *)

let compToString ct = match ct with
    | EQ -> " = "
    | LESS -> " < "
    | GEQ -> " >= "
    | GRT -> " > "
    | LEQ -> " <= "
    | NEQ -> " <> "

let clsTypeToString ty = match ty with 
    | DEF -> " := "
    | LOL -> " :- "

let rec basicTypeToString btyp = match btyp with
	| TKIND (x) -> x
	| TINT -> "int"
	| TSTRING -> "string"
	| TPRED -> "o"
  | TSUBEX -> "tsub"
	| TLIST (x) -> "(list "^(basicTypeToString x)^") "

let rec typeToString typ = match typ with 
	| TBASIC (x) -> basicTypeToString x
	| ARR (x,y) -> 
    match x with
      | TBASIC _ -> (typeToString x)^" -> "^(typeToString y)
      | _ -> "("^(typeToString x)^") -> "^(typeToString y)

let rec termToString term = match term with 
  | VAR v -> 
		if v.tag = EIG then 
			( (v.str)^"EIG_"^(string_of_int v.id) ) 
		else ( (v.str)^"LOG_"^(string_of_int v.id) )
  | DB (i) -> ( "_DB"^(string_of_int i) )
  | INT (x) -> string_of_int x
  | CONS (x) -> x
  | STRING (x) -> x
  | APP (x, y) -> 
    let args = List.fold_right (fun el acc -> "("^(termToString el)^") "^acc) y "" in
    ( (termToString x)^" "^args )
  | ABS (x, i, y) -> "(/lam"^x^(string_of_int i)^" "^(termToString y)^")" 
  | PLUS (ib1, ib2) -> (termToString ib1)^" + "^(termToString ib2)
  | MINUS (ib1, ib2) -> (termToString ib1)^" - "^(termToString ib2)
  | TIMES (ib1, ib2) -> (termToString ib1)^" * "^(termToString ib2)
  | DIV (ib1, ib2) -> (termToString ib1)^" / "^(termToString ib2)

  | SUSP (t, ol, nl, env) -> 
    begin
      match t with 
      | DB i ->
        begin 
          match List.nth env (i-1) with 
          | Binding(t_bind, j) ->  termToString t_bind
          | _ -> termToString t
        end
      | _ -> termToString t
    end
  | PTR {contents = T t} -> termToString t
  | PTR {contents = V v} ->  termToString (VAR v)
  | PRED (s, t, _) -> termToString t
  | EQU (s, i, t) -> " eq prop "^(termToString t)^(string_of_int i)
  | TOP -> "top"
  | ONE -> "one"
  | BOT -> "bot"
  | ZERO -> "zero"
  | NOT (t) -> "not ("^(termToString t)^") "
  | COMP (c, i1, i2) -> (termToString i1)^(compToString c)^(termToString i2)
  | ASGN ( i1, i2) -> (termToString i1)^" is "^(termToString i2)
  | PRINT (t1) -> "print "^(termToString t1)
  | CUT -> "fail(cut)"
  | TENSOR (t1, t2) -> (termToString t1)^" * "^(termToString t2)
  | ADDOR (t1, t2) -> (termToString t1)^" + "^(termToString t2)
  | PARR (t1, t2) -> (termToString t1)^" | "^(termToString t2)
  | LOLLI (s, t1, t2) -> (termToString t2)^" ["^(termToString s)^"] o- "^(termToString t1)
  | BANG (s, t) -> " ["^(termToString s)^"]! "^(termToString t)
  | HBANG (s, t) -> " ["^(termToString s)^"]^! "^(termToString t)
  | QST (s, t) -> " ["^(termToString s)^"]? "^(termToString t)
  | WITH (t1, t2) -> (termToString t1)^" & "^(termToString t2)
  | FORALL (s, i, t) -> "forall "^s^(string_of_int i)^" "^(termToString t)
  | EXISTS (s, i, t) -> "exists "^s^(string_of_int i)^" "^(termToString t)
  | CLS (ty, t1, t2) -> (termToString t1)^(clsTypeToString ty)^(termToString t2)
  | NEW (s, t) -> "new /lam "^s^(termToString t)
  | BRACKET (f) -> "{ "^(termToString f)^" }"

let termsListToString args = List.fold_right (fun el acc ->
  (termToString el)^" :: "^acc) args ""

let subexpTypeToString tp = match tp with
  | LIN -> "lin"
  | UNB -> "unb"
  | REL -> "rel"
  | AFF -> "aff"


(* Modified functions to transform formulas to LaTeX code *)

let compToTexString ct = match ct with
    | EQ -> " = "
    | LESS -> " < "
    | GEQ -> " \\geq "
    | GRT -> " > "
    | LEQ -> " \\leq "
    | NEQ -> " \\neq "

let rec termToTexString term = match term with 
  | VAR v -> 
		if v.tag = EIG then 
			( (v.str)^"EIG-"^(string_of_int v.id) ) 
		else ( (v.str)^"LOG-"^(string_of_int v.id) )
  | DB (i) -> ( "-DB"^(string_of_int i) )
  | INT (x) -> string_of_int x
  | CONS (x) -> x
  | STRING (x) -> x 
  | APP (x, y) -> 
    let args = List.fold_right (fun el acc -> "("^(termToTexString el)^") "^acc) y "" in
    ( (termToTexString x)^" "^args )
  | ABS (x, i, y) -> "(\\lambda "^x^(string_of_int i)^" "^(termToTexString y)^")" 
  | PLUS (ib1, ib2) -> (termToTexString ib1)^" + "^(termToTexString ib2)
  | MINUS (ib1, ib2) -> (termToTexString ib1)^" - "^(termToTexString ib2)
  | TIMES (ib1, ib2) -> (termToTexString ib1)^" \\times "^(termToTexString ib2)
  | DIV (ib1, ib2) -> (termToTexString ib1)^" \\div "^(termToTexString ib2)

  | SUSP (t, ol, nl, env) -> 
    begin
      match t with 
      | DB i ->
        begin 
          match List.nth env (i-1) with 
          | Binding(t_bind, j) ->  termToTexString t_bind
          | _ -> termToTexString t
        end
      | _ -> termToTexString t
    end
  | PTR {contents = T t} -> termToTexString t
  | PTR {contents = V v} ->  termToTexString (VAR v)
  | PRED (s, t, _) -> termToTexString t
  | EQU (s, i, t) -> " eq prop "^(termToTexString t)^(string_of_int i)
  | TOP -> "\\top"
  | ONE -> "1"
  | BOT -> "\\bot"
  | ZERO -> "0"
  | NOT (t) -> "\\neg "^(termToTexString t)
  | COMP (c, i1, i2) -> (termToTexString i1)^(compToTexString c)^(termToTexString i2)
  | ASGN ( i1, i2) -> (termToTexString i1)^" is "^(termToTexString i2)
  | PRINT (t1) -> "print "^(termToTexString t1)
  | CUT -> "fail(cut)"
  | TENSOR (t1, t2) -> (termToTexString t1)^" \\otimes "^(termToTexString t2)
  | ADDOR (t1, t2) -> (termToTexString t1)^" \\oplus "^(termToTexString t2)
  | PARR (t1, t2) -> (termToTexString t1)^" \\bindnasrepma "^(termToTexString t2)
  | LOLLI (s, t1, t2) -> (termToTexString t2)^" \\multimap_{"^(termToTexString s)^"} "^(termToTexString t1)
  | BANG (s, t) -> " !^{"^(termToTexString s)^"} "^(termToTexString t)
  | HBANG (s, t) -> " !^{\\hat{"^(termToTexString s)^"}} "^(termToTexString t)
  | QST (s, t) -> " ?^{"^(termToTexString s)^"} "^(termToTexString t)
  | WITH (t1, t2) -> (termToTexString t1)^" \\binampersand "^(termToTexString t2)
  | FORALL (s, i, t) -> "\\forall "^s^(string_of_int i)^" "^(termToTexString t)
  | EXISTS (s, i, t) -> "\\exists "^s^(string_of_int i)^" "^(termToTexString t)
  | CLS (ty, t1, t2) -> (termToTexString t1)^(clsTypeToString ty)^(termToTexString t2)
  | NEW (s, t) -> "new \\lambda "^s^(termToTexString t)
  | BRACKET (f) -> "\\{ "^(termToTexString f)^" \\}"

let termsListToTexString args = List.fold_right (fun el acc ->
  (termToTexString el)^" :: "^acc) args ""

let rec typeToTexString typ = match typ with 
	| TBASIC (x) -> basicTypeToString x
	| ARR (x,y) -> 
    match x with
      | TBASIC _ -> (typeToTexString x)^" \\rightarrow "^(typeToTexString y)
      | _ -> "("^(typeToTexString x)^") \\rightarrow "^(typeToTexString y)

let texFileHeader () = (
  "\\documentclass[a4paper, 11pt]{article}\n"^ 
  "\\usepackage[utf8]{inputenc}\n"^ 
  "\\usepackage{amsmath}\n"^
  "\\usepackage{amssymb}\n"^ 
  "\\usepackage{stmaryrd}\n"^ 
  "\\usepackage{proof}\n\n"^
  "\\usepackage[landscape]{geometry}\n\n"^ 
  "\\begin{document}\n{\\tiny\n$$\n")
  
let texFileFooter () = "$$\n}\n\\end{document}"
    

(* Removes special characters from a string *)
(* TODO: naive function. Fix it. *)
let remSpecial s = try match  (String.index s '$') with
  | n -> let cp = String.copy s in
    String.set cp n ' '; cp
  with Not_found -> s
;;


