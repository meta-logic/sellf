(*****************************************)
(*                                       *)
(*  Constraint set for reasoning about   *)
(*  context variables                    *)
(*                                       *)
(*  Giselle Machado Reis                 *)
(*  2013                                 *)
(*                                       *)
(*****************************************)

open Term
open Prints
open Subexponentials

let i = ref 0;;

type ctx = string * int
type constraintpred = 
  | IN of terms * ctx
  | MCTX of terms * ctx
  | ELIN of terms * ctx
  | EMP of ctx
  | UNION of ctx * ctx * ctx
  | ADDFORM of terms * ctx * ctx
  | REQIN of terms * ctx
  | REMOVED of terms * ctx * ctx
 
type constraintset = {
  mutable lst : constraintpred list;
}

let create predlst = {
  lst = predlst
}

let union set1 set2 = create (set1.lst @ set2.lst)

(* Cross product between two sets of sets of constraints *)
let times set1 set2 = List.concat (List.map (fun cst1 ->
  List.map (fun cst2 -> union cst1 cst2) set2
) set1)

let copy cst = create cst.lst

let isEmpty cst = (List.length cst.lst) == 0

let isIn f subexp ctx = 
  let index = ContextSchema.getIndex ctx subexp in
  create [IN(f, (subexp, index))]

let requireIn f subexp ctx =
  let index = ContextSchema.getIndex ctx subexp in
  create [REQIN(f, (subexp, index))]

let remove f subexp oldctx newctx = 
  let oldindex = ContextSchema.getIndex oldctx subexp in
  let newindex = ContextSchema.getIndex newctx subexp in
  create [REMOVED(f, (subexp, oldindex), (subexp, newindex))]

let insert f subexp oldctx newctx = 
  let oldindex = ContextSchema.getIndex oldctx subexp in
  let newindex = ContextSchema.getIndex newctx subexp in
  let middleindex = newindex - 1 in
  create [ELIN(f, (subexp, middleindex));
  UNION((subexp, oldindex), (subexp, middleindex), (subexp, newindex))]

let empty subexp ctx = 
  let index = ContextSchema.getIndex ctx subexp in
  create [EMP(subexp, index)]

(* Creates the union constraints of linear contexts of newctx1 and newctx2
  resulting in contexts of ctx *)
let split ctx newctx1 newctx2 =
  let contexts = ContextSchema.getContexts ctx in
  let cstrlst = List.fold_right (fun (s, i) acc -> 
    let i1 = ContextSchema.getIndex newctx1 s in
    let i2 = ContextSchema.getIndex newctx2 s in
    if (i1 != i2) then
      UNION((s, i1), (s, i2), (s, i)) :: acc
    else acc
  ) contexts [] in
  create cstrlst

(* Creates the emptiness constraints for the bang rule *)
(* GR TODO: check if this creates the constraint that $gamma should be empty *)
let bang ctx subexp = 
  let contexts = ContextSchema.getContexts ctx in
  let cstrlst = List.fold_right (fun (s, i) acc ->
    if s = subexp || (greater_than s subexp) then acc
    else EMP(s, i) :: acc
  ) contexts [] in
  create cstrlst

(* Several sets of constraints are created and a list of constraint sets is
returned *)
let initial ctx f = 
  let contexts = ContextSchema.getContexts ctx in
  (* Suppose the dual of f is in s, generates all the constraints *)
  let isHere (sub, i) dualf = 
    let c1 = match type_of sub with
    | LIN | AFF -> ELIN(dualf, (sub, i))
    | UNB | REL -> MCTX(dualf, (sub, i))
    in
    let empty = List.fold_right (fun (s, i) acc ->
      if s != sub then begin match type_of s with
        | LIN | AFF -> EMP(s, i) :: acc
        | UNB | REL -> acc
      end else acc
    ) contexts []
    in
    c1 :: empty
  in
  let cstrs = List.fold_right (fun c acc ->
    ( isHere c (nnf (NOT(f))) ) :: acc 
  ) contexts [] in
  List.map (fun set -> create set) cstrs

let ctxToTex (s, i) = 
  let news = remSpecial s in
  ("$\\Gamma_{"^news^"}^{"^(string_of_int i)^"}$")

let ctxToStr (s, i) = 
  let news = remSpecial s in
  ""^news^"_"^(string_of_int i)^""

let predToTexString c = match c with
  | IN (t, c) -> 
    "\\item in(" ^ (termToTexString t) ^ ", " ^ (ctxToTex c) ^ ")\n"
  | MCTX (t, c) -> 
    "\\item mctx(" ^ (termToTexString t) ^ ", " ^ (ctxToTex c) ^ ")\n"
  | ELIN (t, c) ->
    "\\item elin(" ^ (termToTexString t) ^ ", " ^ (ctxToTex c) ^ ")\n"
  | EMP (c) -> 
    "\\item emp(" ^ (ctxToTex c) ^ ").\n"
  | UNION (c1, c2, c3) -> 
    "\\item union(" ^ (ctxToTex c1) ^ ", " ^ (ctxToTex c2) ^ ", " ^ (ctxToTex c3) ^ ").\n"
  | ADDFORM (t, c1, c2) -> 
    "\\item addform(" ^ (termToTexString t) ^ ", " ^ (ctxToTex c1) ^ ", " ^ (ctxToTex c2) ^ ").\n"
  | REQIN (t, c) -> 
    "\\item requiredIn(" ^ (termToTexString t) ^ ", " ^ (ctxToTex c) ^ ")\n"
  | REMOVED (t, c1, c2) -> 
    "\\item removed(" ^ (termToTexString t) ^ ", " ^ (ctxToTex c1) ^ ", " ^ (ctxToTex c2) ^ ").\n"

let rec toTexString csts = 
  "\\begin{itemize}.\n" ^ 
  (List.fold_right (fun c str -> (predToTexString c) ^ str) csts.lst "") 
  ^ "\\end{itemize}.\n"

let predToString c = match c with
  | IN (t, c) -> 
    "in(\"" ^ (termToString t) ^ "\", " ^ (ctxToStr c) ^ ")."
  | MCTX (t, c) -> 
    "mctx(\"" ^ (termToString t) ^ "\", " ^ (ctxToStr c) ^ ")."
  | ELIN (t, c) ->
    "elin(\"" ^ (termToString t) ^ "\", " ^ (ctxToStr c) ^ ")."
  | EMP (c) ->
    "emp(" ^ (ctxToStr c) ^ ")."
  | UNION (c1, c2, c3) -> 
    "union(" ^ (ctxToStr c1) ^ ", " ^ (ctxToStr c2) ^ ", " ^ (ctxToStr c3) ^ ")."
  | ADDFORM (t, c1, c2) -> 
    "addform(\"" ^ (termToString t) ^ "\", " ^ (ctxToStr c1) ^ ", " ^ (ctxToStr c2) ^ ")."
  | REQIN (t, c) -> 
    "requiredIn(\"" ^ (termToString t) ^ "\", " ^ (ctxToStr c) ^ ")."
  | REMOVED (t, c1, c2) -> 
    "removed(\"" ^ (termToString t) ^ "\", " ^ (ctxToStr c1) ^ ", " ^ (ctxToStr c2) ^ ")."

let toString csts = 
  List.fold_right (fun c str -> 
    (predToString c) ^ "\n" ^ str
  ) csts.lst ""

(*
(* Print constraints to a file *)
let rec printToFile cst out = 
  Printf.fprintf out "%s" (toString cst)

(* Generates a file with the constraint set and the theory specification *)
let genFile cstrSet name = 
  let file = open_out ("solver/"^name^".in") in
  Printf.fprintf file "%s" description;
  Printf.fprintf file "%s" union_clauses_set;
  Printf.fprintf file "%s" elin_clauses_set;
  Printf.fprintf file "%s" emp_clauses_set;
  Printf.fprintf file "%s" mctx_clauses_set;
  Printf.fprintf file "%s" addform_clauses_set;
  Printf.fprintf file "%s" aux_clauses_set;
  printToFile cstrSet file;
  close_out file

(* Get the models from one set of constraints *)
(* This function will return a list of models. These models are represented
as strings which are the true predicated in the format of facts (e.g.
"pred(a). pred(b)." *)
let getModels cstrSet = 
  genFile cstrSet "temp";
  (*let sedStr = " | sed \"s/{//\" | sed \"s/}/./\" | sed \"s/[a-zA-Z]*\\(\\), /. /g\" " in
  let channel = Unix.open_process_in ("dlv -silent solver/temp.in"^sedStr) in*)
  let channel = Unix.open_process_in ("dlv -silent solver/temp.in") in
  let rec readModel input = try match input_line input with
    | str -> (*str :: readModel input*)
      let lexbuf = Lexing.from_string str in
      let model = Parser_models.model Lexer_models.token lexbuf in
      (create model) :: readModel input
    with End_of_file -> let _ = Unix.close_process_in channel in []
  in
  readModel channel
*)


