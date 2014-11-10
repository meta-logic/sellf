(*****************************************)
(*                                       *)
(*  Constraint set for reasoning about   *)
(*  context variables                    *)
(*                                       *)
(*  Giselle Machado Reis                 *)
(*  2013                                 *)
(*                                       *)
(*****************************************)

open ContextSchema (* Remove this dependency *)
open Types
open Term
open Prints
open Subexponentials

let i = ref 0;;

type ctx = string * int
type constraintpred = 
  | IN of terms * ctx
  | EMP of ctx
  | UNION of ctx * ctx * ctx
  | SETMINUS of ctx * terms * ctx
  | REQIN_UNB of terms * ctx (* printed as ":- not in(term, ctx)."*)
  | REQIN_LIN of terms * ctx (* printed as ":- not in(term, ctx). :- in(F, G), in(F', G), F != F'."*)
 
type constraintset = {
  mutable lst : constraintpred list;
}

let create predlst = {
  lst = predlst
}

let union set1 set2 = create (set1.lst @ set2.lst)

let times set1 set2 = List.concat (List.map (fun cst1 ->
  List.map (fun cst2 -> union cst1 cst2) set2
) set1)

(* TODO: check if this method is actually needed *)
let copy cst = create cst.lst

let isEmpty cst = (List.length cst.lst) == 0

let isIn f subexp ctx = 
  let index = ContextSchema.getIndex ctx subexp in
  try match Subexponentials.getCtxArity subexp with
    | MANY | SINGLE -> create [IN(f, (subexp, index))]
    with _ -> failwith "Not applicable: cannot insert formula in context."
;;

(* TODO: decent error handling. *)
let inEndSequent spec ctx = 
  let head = Specification.getPred spec in
  let side = Specification.getSide head in
  let main = Prints.termToTexString(Term.getOnlyRule(Term.formatForm head)) in
  let conDeclared s = Hashtbl.mem Subexponentials.conTbl s in
  List.fold_right (fun (s, i) acc -> 
    let conList = try Hashtbl.find Subexponentials.conTbl s with Not_found -> [] in
    if s = "$gamma" || s = "$infty" then acc
    else try match (getCtxSide s, conDeclared s, conList) with
      | (RIGHTLEFT, false, _) -> (isIn head s ctx) :: acc
      | (RIGHT, false, _) when side  = "rght" -> (isIn head s ctx) :: acc
      | (LEFT, false, _) when side = "lft" -> (isIn head s ctx) :: acc
      | (RIGHTLEFT, true, lst) when List.mem main lst ->(isIn head s ctx) :: acc
      | (RIGHT, true, lst) when side  = "rght" && List.mem main lst -> (isIn head s ctx) :: acc
      | (LEFT, true, lst) when side = "lft" && List.mem main lst ->(isIn head s ctx) :: acc
      | _ -> acc
      with _ -> acc
  ) (ContextSchema.getContexts ctx) []
;;

let insert f subexp oldctx newctx = 
  let oldindex = ContextSchema.getIndex oldctx subexp in
  let newindex = ContextSchema.getIndex newctx subexp in
  create [SETMINUS((subexp, newindex), f, (subexp, oldindex))]

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
let bang ctx subexp = 
  let contexts = ContextSchema.getContexts ctx in
  let cstrlst = List.fold_right (fun (s, i) acc ->
    if s = subexp || (greater_than s subexp) then acc
    else EMP(s, i) :: acc
  ) contexts [] in
  create cstrlst

let requireIn f (subexp, i) = match type_of subexp with
  | AFF | LIN -> REQIN_LIN(f, (subexp, i))
  | REL | UNB -> REQIN_UNB(f, (subexp, i))

(* Several sets of constraints are created and a list of constraint sets is
returned *)
let initial ctx f = 
  let contexts = ContextSchema.getContexts ctx in
  (* Suppose the dual of f is in s, generates all the constraints *)
  let isHere (sub, i) dualf = 
    let empty = List.fold_right (fun (s, i) acc ->
      if s != sub then begin match type_of s with
        | LIN | AFF -> EMP(s, i) :: acc
        | UNB | REL -> acc
      end else acc
    ) contexts []
    in
    (requireIn dualf (sub, i)) :: empty
  in
  let cstrs = List.fold_right (fun c acc ->
    let formSide = Specification.getSide (Specification.getPred (nnf (NOT f))) in
  (* Gamma and infty contexts aren't being processed. If the theory isn't bipole, this is wrong. *)
    if (fst(c)) = "$gamma" || (fst(c)) = "$infty" || not (Subexponentials.isSameSide (fst(c)) formSide) then acc
    else ( isHere c (nnf (NOT(f))) ) :: acc 
  ) contexts [] in
  List.map (fun set -> create set) cstrs

let predToTexString c = match c with
  | IN (t, c) -> 
    "$in(" ^ (termToTexString t) ^ ", " ^ (ContextSchema.ctxToTex c) ^ ").$"
  | SETMINUS (c1, t, c0) ->
    "$minus(" ^ (ContextSchema.ctxToTex c1) ^ ", " ^ (termToTexString t) ^ ", " ^ (ContextSchema.ctxToTex c0) ^ ").$"
  | EMP (c) -> 
    "$emp(" ^ (ContextSchema.ctxToTex c) ^ ").$"
  | UNION (c1, c2, c3) -> 
    "$union(" ^ (ContextSchema.ctxToTex c1) ^ ", " ^ (ContextSchema.ctxToTex c2) ^ ", " ^ (ContextSchema.ctxToTex c3) ^ ").$"
  | REQIN_UNB (t, c) -> 
    "$requiredInUnb(" ^ (termToTexString t) ^ ", " ^ (ContextSchema.ctxToTex c) ^ ") (:- not in()).$"
  | REQIN_LIN (t, c) -> 
    "$requiredInLin(" ^ (termToTexString t) ^ ", " ^ (ContextSchema.ctxToTex c) ^ ") (:- not in(F, G). :- in(F, G), in(F', G), F != F'.).$"


let rec toTexString csts = 
  (List.fold_right (fun c str -> (predToTexString c) ^ "\n\n" ^ str) csts.lst "") 

let predToString c = match c with
  | IN (t, c) -> 
    "in(\"" ^ (termToString t) ^ "\", " ^ (ContextSchema.ctxToStr c) ^ ")."
  | SETMINUS (c1, t, c0) ->
    "minus(" ^ (ContextSchema.ctxToStr c1) ^ ", \"" ^ (termToString t) ^ "\", " ^ (ContextSchema.ctxToStr c0) ^ ")."
  | EMP (c) ->
    "emp(" ^ (ContextSchema.ctxToStr c) ^ ")."
  | UNION (c1, c2, c3) -> 
    "union(" ^ (ContextSchema.ctxToStr c1) ^ ", " ^ (ContextSchema.ctxToStr c2) ^ ", " ^ (ContextSchema.ctxToStr c3) ^ ")."
  | REQIN_UNB (t, c) -> 
    ":- not in(\"" ^ (termToString t) ^ "\", " ^ (ContextSchema.ctxToStr c) ^ ")."
  | REQIN_LIN (t, c) -> 
    ":- not in(\"" ^ (termToString t) ^ "\", " ^ (ContextSchema.ctxToStr c) ^ ").\n" ^
    ":- in(\"" ^ (termToString t) ^ "\", " ^ (ContextSchema.ctxToStr c) ^ "), in(F1, " ^ (ContextSchema.ctxToStr c) ^ "), \"" ^ (termToString t) ^ "\" != F1." 

let toString csts = 
  List.fold_right (fun c str -> 
    (predToString c) ^ "\n" ^ str
  ) csts.lst ""

let isUnion cstr = 
  match cstr with
  | UNION (c2, c3, c1) -> true
  | _ -> false
  
let isIn cstr = 
  match cstr with
  | IN (t, c) -> true
  | _ -> false

let isEmp cstr = 
  match cstr with
  | EMP (c) -> true
  | _ -> false
  
let isMinus cstr = 
  match cstr with
  | SETMINUS (c1, t, c2) -> true
  | _ -> false
  
let isUnbounded cstr = 
  match cstr with
  | UNION (c2, c3, (s, i)) -> type_of s = UNB 
  | IN (t, (s, i)) -> type_of s = UNB
  | EMP ((s, i)) -> type_of s = UNB
  | SETMINUS (c1, t, (s, i)) -> type_of s = UNB
  
let isBounded cstr = not (isUnbounded cstr)  
