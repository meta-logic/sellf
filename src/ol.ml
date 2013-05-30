(****************************************************)
(*                                                  *)
(*  Leonardo Lima, 2013                             *)
(*                                                  *)
(*  Implements the Object Logic (OL), solving the   *)
(*  constraints and making each sequent readable.   *)
(*                                                  *)
(****************************************************)

open Llrules
open Prints
open Term
open ContextSchema
open ProofTreeSchema
open Constraints
open Sequent

module OlContext = struct
  
  type ctx = (string * int) * Term.terms list
  
  type context = {
    mutable lst : ctx list;
  }
  
  let create ctxList = {
    lst = List.map (fun ctx -> (ctx, [])) ctxList;
  }
  
  (* This is necessary because the last formulas are DB(i) *)
  let rec getAbsLst f absLst =
    match f with
    | ABS (s, i, t) -> getAbsLst t ([s] @ absLst)
    | EXISTS (s, i, t) -> getAbsLst t ([s] @ absLst)
    | FORALL (s, i, t) -> getAbsLst t ([s] @ absLst)
    | _ -> absLst
  
  let rec formatForm f = 
    match f with 
    | ABS (s, i, t) -> formatForm t
    | PRED (s, t, pol) -> formatForm t
    | APP (t, tlist) -> List.hd tlist
    | _ -> f
  
  let rec getFormSide f =
    match f with
    | EXISTS (s, i, t) -> getFormSide t
    | LOLLI (t1, t2, t3) -> getFormSide t2
    | ABS (s, i, t) -> getFormSide t
    | TENSOR (t1, t2) -> getFormSide t1
    | ADDOR (t1, t2) -> getFormSide t1
    | PARR (t1, t2) -> getFormSide t1
    | WITH (t1, t2) -> getFormSide t1
    | BANG (t1, t2) -> getFormSide t1
    | NOT (t) -> getFormSide t
    | PRED (s, t, pol) -> s
    | _ -> "empty"
  
  (* Remove vertical bar *)
  let formatString str = 
    try String.sub str 0 ((String.length str)-2) with Invalid_argument("String.sub") -> str
  
  let remDolar str = if str = "lr" then "lr" else String.sub str 1 ((String.length str)-1)
  
  let isEmpty ctx str_ctx side = 
    List.exists (fun ((n, i), f) -> n = str_ctx || ((n = ("$empty" ^ (remDolar str_ctx))) && ((getFormSide (List.hd f)) = side))) ctx.lst
  
  let toTexString ctx side = 
    let slotToTex ctx side str_ctx =
    (List.fold_right (fun ((n, i), f) acc ->
      match (n, side, f) with
      | ("$empty",_,_) -> acc
      | ("$emptylr",_,_) -> acc
      | ("$emptygamma",_,_) -> acc
      | ("$emptyinfty",_,_) -> acc
      | (_, "lft", []) -> 
	if n = str_ctx then "\\Gamma_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, " ^ acc
	else acc
      | (_, "lft", f') -> 
	let formula' = (formatForm (List.hd f')) in
	let absLst = (getAbsLst (List.hd f') []) in
	if n = str_ctx then
	  if (getFormSide (List.hd f')) = "lft" then
	  "\\Gamma_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, " ^ 
	  (termToTexString_ formula' absLst) ^ ", " ^ acc
	  else "\\Gamma_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, "
	else acc
      | (_, "rght", []) -> 
	if n = str_ctx then "\\Delta_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, " ^ acc
	else acc
      | (_, "rght", f') ->
	let formula' = (formatForm (List.hd f')) in
	let absLst = (getAbsLst (List.hd f') []) in
	if n = str_ctx then
	  if (getFormSide (List.hd f')) = "rght" then 
	  "\\Delta_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, " ^ 
	  (termToTexString_ formula' absLst) ^ ", " ^ acc
	  else "\\Delta_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, "
	else acc
      | (_, _, _) -> acc
    ) ctx.lst "") ^
    (List.fold_right (fun ((n, i), f) acc ->
      match (n, side, f) with
      | (_, "lft", f') -> 
	if n = "$empty" ^ (remDolar str_ctx) then
	  let formula = List.hd f' in
	  let formula' = formatForm formula in
	  let absLst = getAbsLst formula [] in
	  if ((getFormSide formula) = "lft") then (termToTexString_ formula' absLst) ^ ", " ^ acc 
	  else acc
	else acc
      | (_, "rght", f') -> 
      	if n = "$empty" ^ (remDolar str_ctx) then
	  let formula = List.hd f' in
	  let formula' = formatForm formula in
	  let absLst = getAbsLst formula [] in
	  if ((getFormSide formula) = "rght") then (termToTexString_ formula' absLst) ^ ", " ^ acc 
	  else acc
	else acc
      | (_, _, _) -> "" ^ acc
    ) ctx.lst "") in
    match ((isEmpty ctx "lr" side), (isEmpty ctx "$gamma" side), (isEmpty ctx "$infty" side)) with
    | (true, true, true) -> (formatString (slotToTex ctx side "lr")) ^ " \\mid " ^ (formatString (slotToTex ctx side "$gamma")) ^
    " \\mid " ^ (formatString (slotToTex ctx side "$infty"))
    | (true, false, false) -> (formatString (slotToTex ctx side "lr")) ^ " \\mid \\cdot \\mid \\cdot "
    | (true, true, false) -> (formatString (slotToTex ctx side "lr")) ^ " \\mid " ^ (formatString (slotToTex ctx side "$gamma")) ^ " \\mid \\cdot "
    | (true, false, true) -> (formatString (slotToTex ctx side "lr")) ^ " \\mid \\cdot \\mid " ^ (formatString (slotToTex ctx side "$infty"))
    | (false, true, true) -> " \\cdot \\mid " ^ (formatString (slotToTex ctx side "$gamma")) ^ " \\mid " ^ (formatString (slotToTex ctx side "$infty"))
    | (false, true, false) ->  " \\cdot \\mid " ^ (formatString (slotToTex ctx side "$gamma")) ^ " \\mid \\cdot "
    | (false, false, true) ->  " \\cdot  \\mid \\cdot \\mid " ^ (formatString (slotToTex ctx side "$infty"))
    | (false, false, false) -> " \\cdot \\mid \\cdot \\mid \\cdot "
  
  (* Hack to fix gamma constraints that come without $ *)
  let fixContext ctx =
    if (fst(ctx) = "gamma" || fst(ctx) = "infty") then (("$" ^ (fst(ctx))), snd(ctx))
    else ctx
  
end;;

module OlSequent = struct
  
  type sequent = {
    mutable ctx : OlContext.context;
    goals : terms list;
    pol : phase;
  }
  
  let getContext seq = seq.ctx

  let create context formulas polarity = {
    ctx = context;
    goals = formulas;
    pol = polarity;
  }
  
  let rec formatForm f = 
      match f with 
      | EXISTS (s, i, t) -> formatForm t
      | LOLLI (t1, t2, t3) -> formatForm t2
      | NOT (t) -> formatForm t
      | PRED (s, t, pol) -> formatForm t
      | TENSOR (t1, t2) -> formatForm t1
      | ADDOR (t1, t2) -> formatForm t1
      | PARR (t1, t2) -> formatForm t1
      | WITH (t1, t2) -> formatForm t1
      | APP (t, tlist) -> List.hd tlist
      | _ -> f
  
  let getOnlyRule f = 
    match f with
    | APP (t, tlist) -> t
    | _ -> f
    
  let getMainForm seq = 
    let goal = if seq.goals != [] then List.hd seq.goals else (* Arbitrary term *) ZERO in
    getOnlyRule (formatForm goal)
  
  let toTexString seq = 
    (OlContext.toTexString seq.ctx "lft")
    ^ " \\vdash " ^ (OlContext.toTexString seq.ctx "rght")
    
end;;

module OlProofTree = struct
  
  type prooftree = {
    mutable conclusion : OlSequent.sequent;
    mutable tree : prooftree list;
    mutable rule : llrule option
  }
  
  let create sq rl = {
    conclusion = sq;
    tree = [];
    rule = rl;
  }
  
  let getConclusion pt = pt.conclusion  
  
  let toMacroRule olPt = 
    let firstPt = List.hd olPt.tree in
    let rec getOpenLeaves pt = 
      match pt.rule with
      | SOME(rule) -> List.flatten (List.map (fun p -> getOpenLeaves p) pt.tree)
      | NONE -> [pt] in
    let newPremises = getOpenLeaves olPt in
    olPt.conclusion <- firstPt.conclusion;
    olPt.tree <- newPremises
  
  let rec toTexString pt =
    let seq = getConclusion pt in
    let rule = OlSequent.getMainForm seq in
    match pt.rule with
    | SOME(r) ->
      let topproof = match pt.tree with
	| [] -> ""
	| hd::tl -> (toTexString hd)^(List.fold_right (fun el acc -> "\n&\n"^(toTexString el)) tl "") 
      in
      "\\infer[" ^ (termToTexString rule) ^ "_{" ^ (OlContext.getFormSide (List.hd seq.OlSequent.goals)) ^ "}" ^ "]{"^(OlSequent.toTexString (getConclusion pt))^"}\n{"^topproof^"}"
    | NONE -> (OlSequent.toTexString (getConclusion pt))

end;;

module Derivation = struct
  
  let rec transformSequent pt =
    let seq = ProofTreeSchema.getConclusion pt in
    let rule = ProofTreeSchema.getRule pt in
    let ctx = SequentSchema.getContext seq in
    let ctxList = [] in
    let ctxListRef = ref ctxList in
    Hashtbl.iter (fun str1 int1 -> ctxListRef := (str1, int1) :: !ctxListRef) ctx.hash;
    let context = OlContext.create !ctxListRef in
    let goals = SequentSchema.getGoals seq in
    let polarity = SequentSchema.getPhase seq in
    let sequent = OlSequent.create context goals polarity in
    let olPt = OlProofTree.create sequent rule in
    if pt.premises = [] then olPt else
    begin 
      olPt.OlProofTree.tree <- List.map transformSequent pt.premises;
      olPt
    end 
    
  let transformTree bplLst = 
    List.map (fun (pt, model) -> (transformSequent pt, model)) bplLst 
    
  (*  IN(F, Γ ): Γ → Γ, F
      EMP(Γ ): Γ → .
      ELIN(F, Γ ): Γ → F
      UNION(Γ1, Γ2, Γ3): Γ3 → Γ1, Γ2 *)
  
  (*let solveMctx olPt c t = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let newCtx = List.map (fun (olc, f) ->  
      if olc = c then (olc, t :: f) 
      else (olc, f)
    ) olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx*)
    
  let solveElin olPt c t = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let olCtxLst = olCtx.OlContext.lst in
    let newCtx = List.map (fun (olc, f) -> 
      if olc = c then (("$empty" ^ (OlContext.remDolar (fst(c))), 0), t :: f) 
      else (olc, f)
    ) olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx;
    newCtx <> olCtxLst
    
  let solveEmp olPt c = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let olCtxLst = olCtx.OlContext.lst in
    let newCtx = List.map (fun (olc, f) -> 
      if olc = c then (("$empty", 0), []) 
      else (olc, f)
      ) olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx;
    newCtx <> olCtxLst
  
  (*let solveUnion olPt pctx1 pctx2 pctx3 = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let lctx = olCtx.OlContext.lst in
    let solveUnionAux pctx1 pctx2 pctx3 lpctx pctx =
      if pctx = pctx3 then pctx1 :: pctx2 :: lpctx else pctx :: lpctx in
    let lctx' = List.fold_left (solveUnionAux pctx1 pctx2 pctx3) [] lctx in
    olCtx.OlContext.lst <- lctx';
    List.for_all (fun el1 -> 
      (List.mem el1 lctx) = true
    ) lctx'
    lctx' <> lctx*)
    
  let solveUnion olPt c1 c2 c3 = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let lctx = olCtx.OlContext.lst in
    let newCtx = [] in
    let newCtxRef = ref newCtx in
    newCtxRef := lctx;
    List.iter (fun (olc, f) ->
      newCtxRef := List.map (fun (olc', f') -> if (olc' = (fst(c3))) then (("$empty", 0), []) else (olc', f')) !newCtxRef;
      if (olc = (fst(c3))) then
	newCtxRef := c1 :: c2 :: !newCtxRef
      else ()
    ) lctx;
    olCtx.OlContext.lst <- !newCtxRef;
    !newCtxRef <> lctx
    
  let solveIn olPt c t = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let olCtxLst = olCtx.OlContext.lst in
    let newCtx = List.map (fun (olc, f) ->  
      if olc = c then
      (* Hack to don't process formulas with the predicate EXISTS *)
      match t with
	| EXISTS (s, i, t) -> (olc, f)
	| _ -> (olc, t :: f)
      else (olc, f)
    ) olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx;
    newCtx <> olCtxLst 
   
  (* First phase *)
  let solveFirstPhase olBipole =
    let cstrRemnant = [] in
    let cstrRemnantRef = ref cstrRemnant in
    let rewSeq seq cstr = 
      match cstr with 
      | ELIN (t, c) -> solveElin seq (OlContext.fixContext c) t
      | EMP (c) -> solveEmp seq (OlContext.fixContext c)
      | UNION (c1, c2, c3) ->
	  let c3' = OlContext.fixContext c3 in
	  let c2' = OlContext.fixContext c2 in
	  let c1' = OlContext.fixContext c1 in
	  solveUnion seq (c1', []) (c2', []) (c3', [])
      | _ -> false in
    let solveConstraints cstr olProofTree =
      match cstr with
      | ELIN (t, c) -> 
	let rec rewTreeElin olTree =
	  rewSeq olTree cstr ::
	  List.concat (List.map rewTreeElin olTree.OlProofTree.tree) in
	let boolList = rewTreeElin olProofTree in
	List.exists (fun el -> el = true) boolList
	  
      | EMP (c) -> 
	let rec rewTreeEmp olTree =
	  rewSeq olTree cstr ::
	  List.concat (List.map rewTreeEmp olTree.OlProofTree.tree) in
	let boolList = rewTreeEmp olProofTree in
	List.exists (fun el -> el = true) boolList
	
      | UNION (c1, c2, c3) ->
	let rec rewTreeUnion olTree = 
	  rewSeq olTree cstr ::
	  List.concat (List.map rewTreeUnion olTree.OlProofTree.tree) in
	let boolList = rewTreeUnion olProofTree in
	List.exists (fun el -> el = true) boolList
	  
      | _ -> false in
    List.iter (fun (olProofTree, model) ->
      List.iter (fun cstr -> 
	if (solveConstraints cstr olProofTree) then ()
	else match cstr with
	| ELIN (t, c) -> cstrRemnantRef := cstr :: !cstrRemnantRef
	| EMP (c) -> cstrRemnantRef := cstr :: !cstrRemnantRef
	| UNION (c1, c2, c3) -> cstrRemnantRef := cstr :: !cstrRemnantRef
	| _ -> ();
	List.iter (fun c -> if (solveConstraints c olProofTree) then () else ()) !cstrRemnantRef;
      ) model.lst;
    ) olBipole
    
  (* Second phase *)     
  let solveSndPhase olBipole =
    let cstrRemnant = [] in
    let cstrRemnantRef = ref cstrRemnant in
    let rewSeq seq cstr = 
      match cstr with 
      | IN (t, c) -> solveIn seq (OlContext.fixContext c) t
      | _ -> false in
    let solveConstraints cstr olProofTree =
      match cstr with
      | IN (t, c) -> 
	let rec rewTreeIn olTree = 
	  rewSeq olTree cstr ::
	  List.concat (List.map rewTreeIn olTree.OlProofTree.tree) in
	let boolList = rewTreeIn olProofTree in
	List.exists (fun el -> el = true) boolList
      | _ -> false in
    List.iter (fun (olProofTree, model) ->
      List.iter (fun cstr ->
    	if (solveConstraints cstr olProofTree) then ()
	else match cstr with
	| IN (t, c) -> cstrRemnantRef := cstr :: !cstrRemnantRef
	| _ -> () 
          ) model.lst;
      List.iter (fun e -> if (solveConstraints e olProofTree) then () else ()) !cstrRemnantRef;
    ) olBipole
    
end;;
