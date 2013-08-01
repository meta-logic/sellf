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
  
  let remComma str = 
    try String.sub str 0 ((String.length str)-2) with Invalid_argument("String.sub") -> str
  
  let remNumberSign str = 
    if (String.get str 0) = '#' then 
      try String.sub str 1 ((String.length str)-1) 
      with Invalid_argument("index out of bounds") -> str
    else str
  
  let remDolar str = 
    if (String.get str 0) = '$' then 
      try String.sub str 1 ((String.length str)-1) 
      with Invalid_argument("index out of bounds") -> str
    else str
    
  (* List all the different context variables *)
  let getStrings ctx = 
    List.fold_right (fun ((n, i), f) acc ->  
      if (List.exists (fun el -> el = (remDolar n)) acc) || 
	(List.exists (fun el -> el = (remNumberSign n)) acc) || n = "#" then acc
	  else if (String.get n 0) = '#' then (remNumberSign n) :: acc
	    else if (String.get n 0) = '$' then (remDolar n) :: acc
	      else n :: acc
    ) ctx.lst []
  
  let isEmpty ctx str_ctx side = 
    List.exists (fun ((n, i), f) -> 
      n = str_ctx || ((n = ("#" ^ (remDolar str_ctx))) && ((getFormSide (List.hd f)) = side))
  ) ctx.lst
  
  let toTexString ctx side = 
    let slotToTex ctx side str_ctx =
    (* Print context variables *)
    (List.fold_right (fun ((n, i), f) acc ->
      match (n, side, f) with
      | ("#",_,_) -> acc
      | ("#lr",_,_) -> acc
      | ("#gamma",_,_) -> acc
      | ("#infty",_,_) -> acc
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
    (* Print formula variables *)
    (List.fold_right (fun ((n, i), f) acc ->
      match (n, side, f) with
      | (_, "lft", f') -> 
	if n = "#" ^ (remDolar str_ctx) then
	  let formula = List.hd f' in
	  let formula' = formatForm formula in
	  let absLst = getAbsLst formula [] in
	  if ((getFormSide formula) = "lft") then (termToTexString_ formula' absLst) ^ ", " ^ acc 
	  else acc
	else acc
      | (_, "rght", f') -> 
      	if n = "#" ^ (remDolar str_ctx) then
	  let formula = List.hd f' in
	  let formula' = formatForm formula in
	  let absLst = getAbsLst formula [] in
	  if ((getFormSide formula) = "rght") then (termToTexString_ formula' absLst) ^ ", " ^ acc 
	  else acc
	else acc
      | (_, _, _) -> "" ^ acc
    ) ctx.lst "") in
    let str_list = getStrings ctx in
    (* Print all slots *)
    List.fold_right (fun str_ctx acc ->
      if (isEmpty ctx str_ctx side) then (remComma (slotToTex ctx side str_ctx)) ^ " \\mid " ^ acc
      else " \\cdot \\mid " ^ acc
    ) str_list ""
  
  (* Hack to fix gamma constraints that come without $ *)
  let fixContext ctx =
    if (fst(ctx) = "gamma" || fst(ctx) = "infty") then (("$" ^ (fst(ctx))), snd(ctx))
    else ctx
  
end;;

module OlSequent = struct
  
  type sequent = {
    mutable ctx : OlContext.context;
    goals : terms list;
    mutable pol : phase;
  }
  
  let getPol seq = seq.pol
  
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
    
  (*let getMainForm seq = 
    let ctx = getContext seq in
    let goal = if seq.goals != [] then List.hd seq.goals else (* Arbitrary term *) ZERO in
    getOnlyRule (formatForm goal)*)
  
  (* Remove the vertical bar remnant *)
  let formatContext str = 
    String.sub str 0 ((String.length str)-6)
  
  let toTexString seq = 
    match seq.pol with
    | ASYN -> (formatContext (OlContext.toTexString seq.ctx "lft"))
    ^ " \\vdash " ^ (formatContext (OlContext.toTexString seq.ctx "rght")) ^ "\\Uparrow"
    | SYNC -> (formatContext (OlContext.toTexString seq.ctx "lft"))
    ^ " \\vdash " ^ (formatContext (OlContext.toTexString seq.ctx "rght")) ^ "\\Downarrow"
    
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
  
  let getPol pt = 
    let conclusion = getConclusion pt in
    conclusion.OlSequent.pol
 
  let toPermutationFormat olPt = 
    let firstPt = List.hd olPt.tree in
    let rec getSwitchedPhase pt = 
      match getPol pt with
      | ASYN ->
	if (List.exists (fun el -> (getPol el) = SYNC) pt.tree) then
	  let nextPt = List.find (fun el -> (getPol el) = SYNC) pt.tree in
	  nextPt.tree <- [];
	  nextPt.rule <- NONE;
	  pt.tree <- [nextPt];
	  [pt]
	else List.concat (List.map (fun p -> getSwitchedPhase p) pt.tree)
      | SYNC -> List.concat (List.map (fun p -> getSwitchedPhase p) pt.tree) in
    let newPt = getSwitchedPhase olPt in
    olPt.conclusion <- firstPt.conclusion;
    olPt.tree <- newPt
    
  let toMacroRule olPt = 
    let firstPt = List.hd olPt.tree in
    let rec getOpenLeaves pt = 
      match pt.rule with
      | SOME(rule) -> List.concat (List.map (fun p -> getOpenLeaves p) pt.tree)
      | NONE -> [pt] in
    let newPremises = getOpenLeaves olPt in
    olPt.conclusion <- firstPt.conclusion;
    olPt.tree <- newPremises
  
  let rec toTexString pt =
    let seq = getConclusion pt in
    (*let rule = OlSequent.getMainForm seq in*)
    match pt.rule with
    | SOME(r) ->
      let topproof = match pt.tree with
	| [] -> ""
	| hd::tl -> (toTexString hd)^(List.fold_right (fun el acc -> "\n&\n"^(toTexString el)) tl "") 
      in
      "\\infer"(* ^ (termToTexString rule) ^ "_{" ^ (OlContext.getFormSide (List.hd seq.OlSequent.goals)) ^ "}" ^*) 
      ^ "{"^(OlSequent.toTexString (getConclusion pt))^"}\n{"^topproof^"}"
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
    
  let transformTree' pair_bpl = 
    List.map (fun ((pt1, model1), (pt2, model2)) ->
      ((transformSequent pt1, model1), (transformSequent pt2, model2))) pair_bpl
    
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
      if olc = c then (("#" ^ (OlContext.remDolar (fst(c))), 0), t :: f) 
      else (olc, f)
    ) olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx;
    newCtx <> olCtxLst
    
  let solveEmp olPt c = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let olCtxLst = olCtx.OlContext.lst in
    let newCtx = List.map (fun (olc, f) -> 
      if olc = c then (("#", 0), []) 
      else (olc, f)
      ) olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx;
    newCtx <> olCtxLst
    
  let solveUnion olPt c1 c2 c3 = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let lctx = olCtx.OlContext.lst in
    let newCtx = [] in
    let newCtxRef = ref newCtx in
    newCtxRef := lctx;
    List.iter (fun (olc, f) ->
      newCtxRef := List.map (fun (olc', f') -> 
      if (olc' = (fst(c3))) then (("#", 0), []) 
      else (olc', f')) !newCtxRef;
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
 
  let rewSeqFst seq cstr = 
    match cstr with 
    | ELIN (t, c) -> solveElin seq (OlContext.fixContext c) t
    | EMP (c) -> solveEmp seq (OlContext.fixContext c)
    | UNION (c1, c2, c3) ->
	let c3' = OlContext.fixContext c3 in
	let c2' = OlContext.fixContext c2 in
	let c1' = OlContext.fixContext c1 in
	solveUnion seq (c1', []) (c2', []) (c3', [])
    | _ -> false
    
  let solveConstraintsFst cstr olProofTree =
    match cstr with
    | ELIN (t, c) -> 
      let rec rewTreeElin olTree =
	rewSeqFst olTree cstr ::
	List.concat (List.map rewTreeElin olTree.OlProofTree.tree) in
      let boolList = rewTreeElin olProofTree in
      List.exists (fun el -> el = true) boolList
	
    | EMP (c) -> 
      let rec rewTreeEmp olTree =
	rewSeqFst olTree cstr ::
	List.concat (List.map rewTreeEmp olTree.OlProofTree.tree) in
      let boolList = rewTreeEmp olProofTree in
      List.exists (fun el -> el = true) boolList
      
    | UNION (c1, c2, c3) ->
      let rec rewTreeUnion olTree = 
	rewSeqFst olTree cstr ::
	List.concat (List.map rewTreeUnion olTree.OlProofTree.tree) in
      let boolList = rewTreeUnion olProofTree in
      List.exists (fun el -> el = true) boolList
      
    | _ -> false
   
  (* First phase: #bipole *)
  let solveFirstPhaseBpl olBipole =
    let cstrRemnant = [] in
    let cstrRemnantRef = ref cstrRemnant in
    List.iter (fun (olProofTree, model) ->
      List.iter (fun cstr -> 
	if (solveConstraintsFst cstr olProofTree) then ()
	else match cstr with
	| ELIN (t, c) -> cstrRemnantRef := cstr :: !cstrRemnantRef
	| EMP (c) -> cstrRemnantRef := cstr :: !cstrRemnantRef
	| UNION (c1, c2, c3) -> cstrRemnantRef := cstr :: !cstrRemnantRef
	| _ -> ();
	List.iter (fun c -> if (solveConstraintsFst c olProofTree) then () else ()) !cstrRemnantRef;
      ) model.lst;
    ) olBipole
    
  (* First phase: #permute *)
  let solveFirstPhasePer pairOfBipoles =
    let cstrRemnant = [] in
    let cstrRemnantRef = ref cstrRemnant in
    let cstrRemnant' = [] in
    let cstrRemnantRef' = ref cstrRemnant' in
    List.iter (fun ((olProofTree1, model1), (olProofTree2, model2)) ->
      let solveModel olProofTree model cstrRemnantRef = 
	List.iter (fun cstr -> 
	  if (solveConstraintsFst cstr olProofTree) then ()
	  else match cstr with
	  | ELIN (t, c) -> cstrRemnantRef := cstr :: !cstrRemnantRef
	  | EMP (c) -> cstrRemnantRef := cstr :: !cstrRemnantRef
	  | UNION (c1, c2, c3) -> cstrRemnantRef := cstr :: !cstrRemnantRef
	  | _ -> ();
	  List.iter (fun c -> if (solveConstraintsFst c olProofTree) then () else ()) !cstrRemnantRef;
	) model.lst in
      solveModel olProofTree1 model1 cstrRemnantRef;
      solveModel olProofTree2 model2 cstrRemnantRef';      
    ) pairOfBipoles
    
  let rewSeqSnd seq cstr = 
    match cstr with 
    | IN (t, c) -> solveIn seq (OlContext.fixContext c) t
    | _ -> false
    
  let solveConstraintsSnd cstr olProofTree =
    match cstr with
    | IN (t, c) -> 
      let rec rewTreeIn olTree = 
	rewSeqSnd olTree cstr ::
	List.concat (List.map rewTreeIn olTree.OlProofTree.tree) in
      let boolList = rewTreeIn olProofTree in
      List.exists (fun el -> el = true) boolList
    | _ -> false
    
  (* Second phase: #bipole *)     
  let solveSndPhaseBpl olBipole =
    let cstrRemnant = [] in
    let cstrRemnantRef = ref cstrRemnant in
    List.iter (fun (olProofTree, model) ->
      List.iter (fun cstr ->
    	if (solveConstraintsSnd cstr olProofTree) then ()
	else match cstr with
	| IN (t, c) -> cstrRemnantRef := cstr :: !cstrRemnantRef
	| _ -> ();
	List.iter (fun e -> if (solveConstraintsSnd e olProofTree) then () else ()) !cstrRemnantRef;
      ) model.lst
    ) olBipole
    
  (* Second phase: #permute *)     
  let solveSndPhasePer pairOfBipoles =
    let cstrRemnant = [] in
    let cstrRemnantRef = ref cstrRemnant in
    let cstrRemnant' = [] in
    let cstrRemnantRef' = ref cstrRemnant' in
    List.iter (fun ((olProofTree1, model1), (olProofTree2, model2)) ->
      let solveModel olProofTree model cstrRemnant =
	List.iter (fun cstr ->
	  if (solveConstraintsSnd cstr olProofTree) then ()
	  else match cstr with
	  | IN (t, c) -> cstrRemnantRef := cstr :: !cstrRemnantRef
	  | _ -> ();
	  List.iter (fun e -> if (solveConstraintsSnd e olProofTree) then () else ()) !cstrRemnantRef;
	) model.lst in
	solveModel olProofTree1 model1 cstrRemnantRef;
	solveModel olProofTree2 model2 cstrRemnantRef';
    ) pairOfBipoles
    
end;;
