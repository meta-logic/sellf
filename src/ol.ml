(*===================*)
(*                     *)
(* Leonardo Lima, 2013 *)
(*                     *)
(*===================*)

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
  
  let toTexString ctx side aux = 
  (List.fold_right (fun ((n, i), f) acc ->
    match (n, side, f) with
    | ("$gamma", _, _) -> acc
    | ("$infty", _, _) -> acc
    | ("lr", "lft", []) -> "\\Delta_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, " ^ acc
    | ("lr", "lft", f') -> let formula' = (formatForm (List.hd f')) in
    let absLst = (getAbsLst (List.hd f') []) in
    "\\Delta_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, " ^ 
    (termToTexString_ formula' absLst) ^ ", " ^ acc
    | ("lr", "rght", []) -> "\\Gamma_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, " ^ acc
    | ("lr", "rght", f') -> let formula' = (formatForm (List.hd f')) in
    let absLst = (getAbsLst (List.hd f') []) in
    "\\Gamma_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, " ^ 
    (termToTexString_ formula' absLst) ^ ", " ^ acc
    | (_, _, _) -> "" ^ acc
  ) ctx.lst "") ^
  (List.fold_right (fun ((n, i), f) acc ->
    match (n, side, f) with
    | ("$empty", "lft", f') -> 
      let formula = List.hd f' in
      let formula' = formatForm formula in
      let absLst = getAbsLst formula [] in
      if ((getFormSide formula) = "lft") then
	match formula with
	| ABS (s, i, t) -> if aux = 0 then acc else (termToTexString_ formula' absLst) ^ ", " ^ acc 
	| PRED (s, t, pol) ->  if aux = 0 then acc else (termToTexString_ formula' absLst) ^ ", " ^ acc 
	| _ -> (termToTexString_ formula' absLst) ^ ", " ^ acc 
      else acc
    | ("$empty", "rght", f') -> 
      let formula = List.hd f' in
      let formula' = formatForm formula in
      let absLst = getAbsLst formula [] in
      if ((getFormSide formula) = "rght") then
	match formula with
	| ABS (s, i, t) -> if aux = 0 then acc else (termToTexString_ formula' absLst) ^ ", " ^ acc 
	| PRED (s, t, pol) ->  if aux = 0 then acc else (termToTexString_ formula' absLst) ^ ", " ^ acc 
	| _ -> (termToTexString_ formula' absLst) ^ ", " ^ acc 
      else acc
    | (_, _, _) -> "" ^ acc
  ) ctx.lst "")
  
  (* Hack to fix gamma constraints that come without $ *)
  let fixGamma ctx =
    ("$gamma", snd(ctx))
  
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
  
  let remComma str = String.sub str 0 ((String.length str)-2)
  
  let rec formatForm' f = 
    match f with
    | NOT (t) -> formatForm' t
    | PRED (s, t, pol) -> formatForm' t
    | APP (t, tlist) -> List.hd tlist
    | _ -> f
  
  let rec formatForm f = 
      match f with 
      | EXISTS (s, i, t) -> formatForm t
      | LOLLI (t1, t2, t3) -> formatForm t2
      | APP (t, tlist) -> formatForm t
      | NOT (t) -> formatForm t
      | PRED (s, t, pol) -> formatForm t
      | TENSOR (t1, t2) -> formatForm' t1
      | ADDOR (t1, t2) -> formatForm' t1
      | PARR (t1, t2) -> formatForm' t1
      | WITH (t1, t2) -> formatForm' t1
      | _ -> f
      
  let getTransformedForm seq = 
    let goal = if seq.goals = [] then ZERO else (List.hd seq.goals) in
    let goal' = formatForm goal in
    let absLst = OlContext.getAbsLst goal [] in
    termToTexString_ goal' absLst
  
  let toTexString seq i = 
    let goal = if seq.goals = [] then ZERO else (List.hd seq.goals) in
    let side = OlContext.getFormSide goal in
    let goalString = getTransformedForm seq in
    match (seq.goals, side) with
    | ([], "empty") -> 
    (remComma (OlContext.toTexString seq.ctx "lft" i)) 
    ^ " \\vdash " ^ (remComma (OlContext.toTexString seq.ctx "rght" i))
    | (_, "lft") -> 
    (remComma (OlContext.toTexString seq.ctx "lft" i)) ^ ", " ^
    (goalString) ^ " \\vdash " ^ (remComma (OlContext.toTexString seq.ctx "rght" i))
    | (_, "rght") -> 
    (remComma (OlContext.toTexString seq.ctx "lft" i)) ^ " \\vdash " ^
    (remComma(OlContext.toTexString seq.ctx "rght" i)) ^ ", " ^ (goalString)
    | (_, _) -> ""
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
  let finalRule = OlSequent.getTransformedForm seq in
  match pt.rule with
  | SOME(r) ->
    let topproof = match pt.tree with
      | [] -> ""
      | hd::tl -> (toTexString hd)^(List.fold_right (fun el acc -> "\n&\n"^(toTexString el)) tl "") 
    in
    (* First sequent: 0 *)
    (* Show formulae with ABS and PRED predicates only in the second sequent *)
    "\\infer[" ^ (finalRule) ^ "]{"^(OlSequent.toTexString (getConclusion pt) 0)^"}\n{"^topproof^"}"
    (* Second sequent: 1 *)
  | NONE -> (OlSequent.toTexString (getConclusion pt) 1)

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
    List.map (fun (pt, model) -> transformSequent pt) bplLst 
    
  (*  IN(F, Γ ): Γ → Γ, F
      MCTX(F, Γ ): Γ → Γ, F
      EMP(Γ ): Γ → .
      ELIN(F, Γ ): Γ → F
      UNION(Γ1, Γ2, Γ3): Γ3 → Γ1, Γ2 *)
  
  let solveMctx olPt c t = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let newCtx = List.map (fun (olc, f) ->  
      if olc = c then (olc, t :: f) 
      else (olc, f)
    ) olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx
    
  let solveElin olPt c t = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let newCtx = List.map (fun (olc, f) -> 
      if olc = c then (("$empty", 0), t :: f) 
      else (olc, f)
    ) olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx
    
  let solveEmp olPt c = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let newCtx = List.filter (fun (olc, f) -> 
      olc != c) olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx
  
  let solveUnionPrime olPt pctx1 pctx2 pctx3 = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let lctx = olCtx.OlContext.lst in
    let solveUnionAux pctx1 pctx2 pctx3 lpctx pctx =
    if pctx = pctx3 then pctx1 :: pctx2 :: lpctx else pctx :: lpctx in
    let lctx' = List.fold_left (solveUnionAux pctx1 pctx2 pctx3) [] lctx in
    olCtx.OlContext.lst <- lctx' 
    
  let solveIn olPt c t = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let newCtx = List.map (fun (olc, f) ->  
      if olc = c then
      (* Hack to don't process formulas with the predicate EXISTS *)
      match t with
	| EXISTS (s, i, t) -> (olc, f)
	| _ -> (olc, t :: f)
      else (olc, f)
    ) olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx
    
  (* First phase *)
  let solveFirstPhase bplLst olProofTree =
    let rewSeq seq cstr = 
      match cstr with 
      | MCTX (t, c) -> 
	  if (fst(c) = "gamma") then
	    let c' = OlContext.fixGamma c in solveMctx seq c' t
	  else solveMctx seq c t
      | ELIN (t, c) -> 
	  if (fst(c) = "gamma") then
	    let c' = OlContext.fixGamma c in solveElin seq c' t
	  else solveElin seq c t
      | EMP (c) ->
	  if (fst(c) = "gamma") then
	    let c' = OlContext.fixGamma c in solveEmp seq c'
	  else solveEmp seq c
      | UNION (c1, c2, c3) ->
	  if (fst(c3) = "gamma") then
	    let c3' = OlContext.fixGamma c3 in
	    let c2' = OlContext.fixGamma c2 in
	    let c1' = OlContext.fixGamma c1 in
	  solveUnionPrime seq (c1', []) (c2', []) (c3', [])
	  else 
	  solveUnionPrime seq (c1, []) (c2, []) (c3, [])
      | _ -> () in
    List.iter (fun (pt, model) ->
    List.iter (fun cstr -> 
      match cstr with
      | MCTX (t, c) -> 
	let rec rewTreeMctx olTree = 
	  rewSeq olTree cstr;
	  List.iter rewTreeMctx olTree.OlProofTree.tree in
	List.iter rewTreeMctx olProofTree
	
      | ELIN (t, c) -> 
	let rec rewTreeElin olTree =
	  rewSeq olTree cstr;
	  List.iter rewTreeElin olTree.OlProofTree.tree in
	List.iter rewTreeElin olProofTree
	  
      | EMP (c) -> 
	let rec rewTreeEmp olTree =
	  rewSeq olTree cstr;
	  List.iter rewTreeEmp olTree.OlProofTree.tree in
	List.iter rewTreeEmp olProofTree
	
      | UNION (c1, c2, c3) ->
	let rec rewTreeUnion olTree = 
	  rewSeq olTree cstr;
	  List.iter rewTreeUnion olTree.OlProofTree.tree in
	List.iter rewTreeUnion olProofTree
	
      | _ -> ()
    ) model.lst ) bplLst
    
  (* Second phase *)     
  let solveSndPhase bplLst olProofTree =
    let rewSeq seq cstr = 
      match cstr with 
      | IN (t, c) -> 
	  if (fst(c) = "gamma") then
	    let c' = OlContext.fixGamma c in solveIn seq c' t
	  else solveIn seq c t
      | _ -> () in
    List.iter (fun (pt, model) ->
    List.iter (fun cstr -> 
      match cstr with
      | IN (t, c) -> 
	let rec rewTreeIn olTree = 
	  rewSeq olTree cstr;
	  List.iter rewTreeIn olTree.OlProofTree.tree in
	List.iter rewTreeIn olProofTree
      | _ -> ()
  ) model.lst ) bplLst
    
end;;