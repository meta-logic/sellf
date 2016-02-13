
(* Giselle Machado Reis - 2012 *)

open Types

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

(* Prints a term replacing deBruijn indices by the actual variable name. This
name is kept in the abstraction, and a stack of abstraction names is passed as
argument *)
let rec termToString_ term absList = match term with 
  | VAR v -> v.str (* Always parsed as a logical variable. Not sure if it will cause any problems... *) 
		(*if v.tag = EIG then 
			( (v.str)^"EIG_"^(string_of_int v.id) ) 
		else ( (v.str)^"LOG_"^(string_of_int v.id) )*)
  | DB (i) -> 
    if (List.length absList) < i then failwith "Fail printing DB indices."
    else List.nth absList (i-1)
  | INT (x) -> string_of_int x
  | CONST (x) -> x
  | STRING (x) -> x
  | APP (x, y) -> 
    let args = List.fold_right (fun el acc -> (termToString_ el absList)^" "^acc) y "" in
    ( "( "^(termToString_ x absList)^" "^args^" )" )
  | ABS (x, i, y) -> "(\\"^x^" "^(termToString_ y ([x] @ absList))^")" 
  | PLUS (ib1, ib2) -> (termToString_ ib1 absList)^" + "^(termToString_ ib2 absList)
  | MINUS (ib1, ib2) -> (termToString_ ib1 absList)^" - "^(termToString_ ib2 absList)
  | TIMES (ib1, ib2) -> (termToString_ ib1 absList)^" * "^(termToString_ ib2 absList)
  | DIV (ib1, ib2) -> (termToString_ ib1 absList)^" / "^(termToString_ ib2 absList)

  | SUSP (t, ol, nl, env) -> 
    begin
      match t with 
      | DB i ->
        begin 
          match List.nth env (i-1) with 
          | Binding(t_bind, j) ->  termToString_ t_bind absList
          | _ -> termToString_ t absList 
        end
      | _ -> termToString_ t absList
    end
  | PTR {contents = T t} -> termToString_ t absList
  | PTR {contents = V v} -> termToString_ (VAR v) absList
  | PRED (s, t, _) -> termToString_ t absList
  | EQU (s, i, t) -> " eq prop "^(termToString_ t absList)^(string_of_int i)
  | TOP -> "top"
  | ONE -> "one"
  | BOT -> "bot"
  | ZERO -> "zero"
  | NOT (t) -> "(not "^(termToString_ t absList)^") "
  | COMP (c, i1, i2) -> (termToString_ i1 absList)^(compToString c)^(termToString_ i2 absList)
  | ASGN ( i1, i2) -> (termToString_ i1 absList)^" is "^(termToString_ i2 absList)
  | PRINT (t1) -> "print "^(termToString_ t1 absList)
  | CUT -> "fail(cut)"
  | TENSOR (t1, t2) -> (termToString_ t1 absList)^" * "^(termToString_ t2 absList)
  | ADDOR (t1, t2) -> (termToString_ t1 absList)^" + "^(termToString_ t2 absList)
  | PARR (t1, t2) -> (termToString_ t1 absList)^" | "^(termToString_ t2 absList)
  | LOLLI (s, t1, t2) -> (termToString_ t2 absList)^" ["^(termToString_ s absList)^"] o- "^(termToString_ t1 absList)
  | BANG (CONST("infty"), t) -> "(bang "^(termToString_ t absList)^" )"
  | HBANG (CONST("infty"), t) -> "(hbang "^(termToString_ t absList)^" )"
  | QST (CONST("infty"), t) -> "(? "^(termToString_ t absList)^" )"
  | BANG (s, t) -> "( ["^(termToString_ s absList)^"]bang "^(termToString_ t absList)^" )"
  | HBANG (s, t) -> "( ["^(termToString_ s absList)^"]hbang "^(termToString_ t absList)^" )"
  | QST (s, t) -> "( ["^(termToString_ s absList)^"]? "^(termToString_ t absList)^" )"
  | WITH (t1, t2) -> (termToString_ t1 absList)^" & "^(termToString_ t2 absList)
  | FORALL (s, i, t) -> "(pi \\"^s^" "^(termToString_ t ([s] @ absList))^")"
  | EXISTS (s, i, t) -> "(sigma \\"^s^" "^(termToString_ t ([s] @ absList))^")"
  | CLS (ty, t1, t2) -> (termToString_ t1 absList)^(clsTypeToString ty)^(termToString_ t2 absList)
  | NEW (s, t) -> "(nsub \\"^s^(termToString_ t ([s] @ absList))^")"
  | BRACKET (f) -> "{ "^(termToString_ f absList)^" }"

let termToString term = termToString_ term []

let termsListToString args = List.fold_right (fun el acc ->
  (termToString el)^" :: "^acc) args ""

(* Modified functions to transform formulas to LaTeX code *)

let compToTexString ct = match ct with
    | EQ -> " = "
    | LESS -> " < "
    | GEQ -> " \\geq "
    | GRT -> " > "
    | LEQ -> " \\leq "
    | NEQ -> " \\neq "

let rec termToTexString_ term absList = match term with 
  | VAR v -> v.str
		(*if v.tag = EIG then 
			( (v.str)^"EIG-"^(string_of_int v.id) ) 
		else ( (v.str)^"LOG-"^(string_of_int v.id) )*)
  | DB (i) ->
    if (List.length absList) < i then failwith "Fail printing DB indices."
    else List.nth absList (i-1)
  | INT (x) -> string_of_int x
  | CONST (x) -> x
  | STRING (x) -> x 
  | APP (x, y) -> 
    let args = List.fold_right (fun el acc -> "("^(termToTexString_ el absList)^") "^acc) y "" in
    ( (termToTexString_ x absList)^" "^args )
  | ABS (x, i, y) -> "(\\lambda "^x^" "^(termToTexString_ y ([x] @ absList))^")" 
  | PLUS (ib1, ib2) -> (termToTexString_ ib1 absList)^" + "^(termToTexString_ ib2 absList)
  | MINUS (ib1, ib2) -> (termToTexString_ ib1 absList)^" - "^(termToTexString_ ib2 absList)
  | TIMES (ib1, ib2) -> (termToTexString_ ib1 absList)^" \\times "^(termToTexString_ ib2 absList)
  | DIV (ib1, ib2) -> (termToTexString_ ib1 absList)^" \\div "^(termToTexString_ ib2 absList)

  | SUSP (t, ol, nl, env) -> 
    begin
      match t with 
      | DB i ->
        begin 
          match List.nth env (i-1) with 
          | Binding(t_bind, j) ->  termToTexString_ t_bind absList
          | _ -> termToTexString_ t absList
        end
      | _ -> termToTexString_ t absList
    end
  | PTR {contents = T t} -> termToTexString_ t absList
  | PTR {contents = V v} ->  termToTexString_ (VAR v) absList
  | PRED (s, t, _) -> termToTexString_ t absList
  | EQU (s, i, t) -> " eq prop "^(termToTexString_ t absList)^(string_of_int i)
  | TOP -> "\\top"
  | ONE -> "1"
  | BOT -> "\\bot"
  | ZERO -> "0"
  | NOT (t) -> "\\neg "^(termToTexString_ t absList)
  | COMP (c, i1, i2) -> (termToTexString_ i1 absList)^(compToTexString c)^(termToTexString_ i2 absList)
  | ASGN ( i1, i2) -> (termToTexString_ i1 absList)^" is "^(termToTexString_ i2 absList)
  | PRINT (t1) -> "print "^(termToTexString_ t1 absList)
  | CUT -> "fail(cut)"
  | TENSOR (t1, t2) -> (termToTexString_ t1 absList)^" \\;\\otimes\\; "^(termToTexString_ t2 absList)
  | ADDOR (t1, t2) -> (termToTexString_ t1 absList)^" \\;\\oplus\\; "^(termToTexString_ t2 absList)
  | PARR (t1, t2) -> (termToTexString_ t1 absList)^" \\;\\mypar\\; "^(termToTexString_ t2 absList)
  | LOLLI (s, t1, t2) -> (termToTexString_ t2 absList)^" \\;\\multimap_{"^(termToTexString_ s absList)^"}\\; "^(termToTexString_ t1 absList)
  | BANG (CONST("infty"), t) -> " ! "^(termToTexString_ t absList)
  | HBANG (CONST("infty"), t) -> " \\hat{!} "^(termToTexString_ t absList)
  | QST (CONST("infty"), t) -> " ? "^(termToTexString_ t absList)
  | BANG (s, t) -> " !^{"^(termToTexString_ s absList)^"} "^(termToTexString_ t absList)
  | HBANG (s, t) -> " !^{\\hat{"^(termToTexString_ s absList)^"}} "^(termToTexString_ t absList)
  | QST (s, t) -> " ?^{"^(termToTexString_ s absList)^"} "^(termToTexString_ t absList)
  | WITH (t1, t2) -> (termToTexString_ t1 absList)^" \\;\\&\\; "^(termToTexString_ t2 absList)
  | FORALL (s, i, t) -> "\\forall\\; "^s^" "^(termToTexString_ t ([s] @ absList))
  | EXISTS (s, i, t) -> "\\exists\\; "^s^" "^(termToTexString_ t ([s] @ absList))
  | CLS (ty, t1, t2) -> (termToTexString_ t1 absList)^(clsTypeToString ty)^(termToTexString_ t2 absList)
  | NEW (s, t) -> "new \\lambda "^s^(termToTexString_ t ([s] @ absList))
  | BRACKET (f) -> "\\{ "^(termToTexString_ f absList)^" \\}"

let termToTexString term = termToTexString_ term []

let termsListToTexString args = List.fold_right (fun el acc ->
  (termToTexString el)^" :: "^acc) args ""

let rec typeToTexString typ = match typ with 
	| TBASIC (x) -> basicTypeToString x
	| ARR (x,y) -> 
    match x with
      | TBASIC _ -> (typeToTexString x)^" \\rightarrow "^(typeToTexString y)
      | _ -> "("^(typeToTexString x)^") \\rightarrow "^(typeToTexString y)

let texFileHeader = (
  "\\documentclass[a4paper, 11pt]{article}\n"^ 
  "\\usepackage[utf8]{inputenc}\n"^ 
  "\\usepackage{amsmath}\n"^
  "\\usepackage{amssymb}\n"^ 
  "\\usepackage{stmaryrd}\n"^ 
  "\\usepackage{proof}\n"^
  "\\usepackage{graphicx}\n"^
  "\\usepackage{color}\n"^
  "\\usepackage[landscape, margin=1cm]{geometry}\n\n"^ 
  "\\newcommand{\\mypar}{\\ensuremath{\\rotatebox[origin=c]{180}{\\&}}}\n\n"^
  "\\begin{document}\n\n")
  
let texFileFooter = "\n\n\\end{document}"

;;
