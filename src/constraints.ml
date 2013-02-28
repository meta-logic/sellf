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
  | REQIN of terms * ctx (* printed as ":- not in(term, ctx)."*)
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

let predToTexString c = match c with
  | IN (t, c) -> 
    "$in(" ^ (termToTexString t) ^ ", " ^ (ContextSchema.ctxToTex c) ^ ").$"
  | MCTX (t, c) -> 
    "$mctx(" ^ (termToTexString t) ^ ", " ^ (ContextSchema.ctxToTex c) ^ ").$"
  | ELIN (t, c) ->
    "$elin(" ^ (termToTexString t) ^ ", " ^ (ContextSchema.ctxToTex c) ^ ").$"
  | EMP (c) -> 
    "$emp(" ^ (ContextSchema.ctxToTex c) ^ ").$"
  | UNION (c1, c2, c3) -> 
    "$union(" ^ (ContextSchema.ctxToTex c1) ^ ", " ^ (ContextSchema.ctxToTex c2) ^ ", " ^ (ContextSchema.ctxToTex c3) ^ ").$"
  | ADDFORM (t, c1, c2) -> 
    "$addform(" ^ (termToTexString t) ^ ", " ^ (ContextSchema.ctxToTex c1) ^ ", " ^ (ContextSchema.ctxToTex c2) ^ ").$"
  | REQIN (t, c) -> 
    "$requiredIn(" ^ (termToTexString t) ^ ", " ^ (ContextSchema.ctxToTex c) ^ ") (:- not in()).$"
  | REMOVED (t, c1, c2) -> 
    "$removed(" ^ (termToTexString t) ^ ", " ^ (ContextSchema.ctxToTex c1) ^ ", " ^ (ContextSchema.ctxToTex c2) ^ ").$"

let rec toTexString csts = 
  (List.fold_right (fun c str -> (predToTexString c) ^ ", " ^ str) csts.lst "") 

let predToString c = match c with
  | IN (t, c) -> 
    "in(\"" ^ (termToString t) ^ "\", " ^ (ContextSchema.ctxToStr c) ^ ")."
  | MCTX (t, c) -> 
    "mctx(\"" ^ (termToString t) ^ "\", " ^ (ContextSchema.ctxToStr c) ^ ")."
  | ELIN (t, c) ->
    "elin(\"" ^ (termToString t) ^ "\", " ^ (ContextSchema.ctxToStr c) ^ ")."
  | EMP (c) ->
    "emp(" ^ (ContextSchema.ctxToStr c) ^ ")."
  | UNION (c1, c2, c3) -> 
    "union(" ^ (ContextSchema.ctxToStr c1) ^ ", " ^ (ContextSchema.ctxToStr c2) ^ ", " ^ (ContextSchema.ctxToStr c3) ^ ")."
  | ADDFORM (t, c1, c2) -> 
    "addform(\"" ^ (termToString t) ^ "\", " ^ (ContextSchema.ctxToStr c1) ^ ", " ^ (ContextSchema.ctxToStr c2) ^ ")."
  | REQIN (t, c) -> 
    ":- not in(\"" ^ (termToString t) ^ "\", " ^ (ContextSchema.ctxToStr c) ^ ")."
  | REMOVED (t, c1, c2) -> 
    "removed(\"" ^ (termToString t) ^ "\", " ^ (ContextSchema.ctxToStr c1) ^ ", " ^ (ContextSchema.ctxToStr c2) ^ ")."

let toString csts = 
  List.fold_right (fun c str -> 
    (predToString c) ^ "\n" ^ str
  ) csts.lst ""


