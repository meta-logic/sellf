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
    | APP (t, tlist) -> getFormSide t
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
    | CONS (s) -> s
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
    
  let getFormString f side = 
    let formList = List.map (fun f' -> (f', (getAbsLst f' []))) f in
    (List.fold_right (fun (form, absLst) acc' ->
      if (getFormSide form) = side then (termToTexString_ (formatForm form) absLst) ^ ", " ^ acc'
      else acc'
    ) formList "")
  
  let toTexString ctx side str_list = 
    let slotToTex ctx side str_ctx =
    (* Print context variables *)
    (List.fold_right (fun ((n, i), f) acc ->
      match (n, side, f) with
      | ("#",_,_) -> acc
      | ("#lr",_,_) -> acc
      | ("#gamma",_,_) -> acc
      | ("#infty",_,_) -> acc
      | (_, "lft", []) -> 
	if n = str_ctx then
	  "\\Gamma_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, " ^ acc
	else acc
      | (_, "lft", f') -> 
	if n = str_ctx then
	  begin
	    let initialString = "\\Gamma_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, " in
	    initialString ^ (getFormString f' "lft") ^ acc
	  end
	else acc
      | (_, "rght", []) -> 
	if n = str_ctx then 
	  "\\Delta_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, " ^ acc
	else acc
      | (_, "rght", f') ->
	if n = str_ctx then
	  begin
	    let initialString = "\\Delta_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "}, " in
	    initialString ^ (getFormString f' "rght") ^ acc
	  end
	else acc
      | (_, _, _) -> acc
    ) ctx.lst "") ^
    (* Print formula variables *)
    (List.fold_right (fun ((n, i), f) acc ->
      match (n, side, f) with
      | (_, "lft", f') -> 
	if n = "#" ^ (remDolar str_ctx) then
	  (getFormString f' "lft") ^ acc
	else acc
      | (_, "rght", f') -> 
      	if n = "#" ^ (remDolar str_ctx) then
	  (getFormString f' "rght") ^ acc
	else acc
      | (_, _, _) -> "" ^ acc
    ) ctx.lst "") in
    (* Print all slots *)
    List.fold_right (fun str_ctx acc ->
      let slotString = remComma (slotToTex ctx side str_ctx) in
      match slotString with
      | "" -> " \\cdot \\mid " ^ acc
      | slotString' -> slotString' ^ " \\mid " ^ acc
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
    
  let getMainForm seq = 
    match seq.goals with
    | [] -> NONE
    | _ -> SOME (getOnlyRule (formatForm (List.hd seq.goals)))
  
  (* Remove the vertical bar remnant *)
  let formatContext str = 
    String.sub str 0 ((String.length str)-6)
  
  let toTexString seq str_list = 
  match (getPol seq) with
  | ASYN -> (formatContext (OlContext.toTexString seq.ctx "lft" str_list))
    ^ " \\vdash " ^ (formatContext (OlContext.toTexString seq.ctx "rght" str_list)) (*^ " \\Uparrow "*)
  | SYNC -> (formatContext (OlContext.toTexString seq.ctx "lft" str_list))
    ^ " \\vdash " ^ (formatContext (OlContext.toTexString seq.ctx "rght" str_list)) (*^  " \\Downarrow "*)
    
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
  
  let getFromOption opt = 
    match opt with
    | SOME(x) -> x
    | NONE -> raise (Invalid_argument "Option.get")
  
  let getConclusion pt = pt.conclusion
  
  let getContextFromPt pt = OlSequent.getContext (getConclusion pt) 
  
  let getRule pt = pt.rule
  
  let getPol pt = 
    let conclusion = getConclusion pt in
    conclusion.OlSequent.pol
    
  let getListFromOptions lst = 
    List.concat (List.map (fun el ->
      match el with
      | SOME (el') -> [getFromOption el]
      | NONE -> []
    ) lst )
 
  let toPermutationFormat olPt = 
    let firstPt = List.hd olPt.tree in
    let rec getSeq' pt = 
      match (pt.tree, getPol pt) with 
      | ([], ASYN) -> 
	begin
	  match pt.rule with 
	  | SOME(r) -> [NONE]
	  | NONE -> [SOME(pt)]
	end
      | (lpt, _) -> List.concat (List.map (fun p -> getSeq' p) lpt) in      
    let rec getSeq pt' =
      let pt = getFromOption pt' in
      match pt.tree with
      | [] -> 
	begin
	  match (getRule pt) with 
	  | SOME(r) -> [NONE]
	  | NONE -> [SOME(pt)]
	end
      | _ -> 
	begin
	  match (getPol pt) with
	  | ASYN ->
	    if (List.exists (fun el -> (getPol el) = SYNC) pt.tree) then
	      let nextPt = List.find (fun el -> (getPol el) = SYNC) pt.tree in
	      nextPt.tree <- List.concat (List.map (fun el -> match el with
		| SOME (el') -> [getFromOption el]
		| NONE -> [] 
		) (getSeq' nextPt));
	      [SOME(nextPt)]
	    else let tree_opt = List.map (fun el -> SOME(el)) pt.tree in
	    List.concat (List.map (fun p -> getSeq p) tree_opt)
	  | SYNC -> 
	    let tree_opt = List.map (fun el -> SOME(el)) pt.tree in
	    List.concat (List.map (fun p -> getSeq p) tree_opt)
	  end in  
    let newPtList = getSeq (SOME(firstPt)) in
    olPt.tree <- (getListFromOptions newPtList);
    olPt.conclusion <- firstPt.conclusion
    
  let toMacroRule olPt = 
    let firstPt = List.hd olPt.tree in
    let rec getOpenLeaves pt = 
      match pt.rule with
      | SOME(rule) -> List.concat (List.map (fun p -> getOpenLeaves p) pt.tree)
      | NONE -> [pt] in
    let newPremises = getOpenLeaves olPt in
    olPt.conclusion <- firstPt.conclusion;
    olPt.tree <- newPremises
    
  let collectStrings pt =
    let conclusion = getConclusion pt in
    let context = OlSequent.getContext conclusion in
    (OlContext.getStrings context)
    
  let sideToChar side = 
    match side with
    | "rght" -> "R"
    | "lft" -> "L"
    | _ -> ""
  
  let toTexString pt =
    let str_list = collectStrings pt in
    let rec toTexString' pt = 
      match pt.rule with
      | SOME(r) ->
	      let seq = getConclusion pt in
	      let rule = getFromOption (OlSequent.getMainForm seq) in
	      let topproof = match pt.tree with
	        | [] -> ""
	        | hd::tl -> (toTexString' hd)^(List.fold_right (fun el acc -> "\n&\n"^(toTexString' el)) tl "") 
	      in
        let ruleNameTex = (termToTexString rule) ^ "_{" ^ (sideToChar (OlContext.getFormSide (List.hd seq.OlSequent.goals))) ^ "}" in
	      (*"\\infer[" ^ ruleNameTex ^ "]{" ^ (OlSequent.toTexString (getConclusion pt) str_list) ^ "}\n{" ^ topproof ^ "}"*)
	      "\\cfrac{" ^ topproof ^ "}\n{" ^ (OlSequent.toTexString (getConclusion pt) str_list) ^ "} \;\; " ^ ruleNameTex 
      | NONE -> (OlSequent.toTexString (getConclusion pt) str_list) 
    in
    toTexString' pt

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
    let newPair = List.map (fun (olc, f) -> 
      if olc = c then ((("#" ^ (OlContext.remDolar (fst(c))), 0), t :: f), true)
      else ((olc, f), false)
    ) olCtx.OlContext.lst in
    let isDiff = List.exists (fun el -> (snd(el)) = true) newPair in
    let newCtx = List.map (fun el -> fst(el)) newPair in
    olCtx.OlContext.lst <- newCtx;
    isDiff
    
  let solveEmp olPt c = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let newPair = List.map (fun (olc, f) -> 
      if olc = c then ((("#", 0), []), true) 
      else ((olc, f), false)
      ) olCtx.OlContext.lst in
    let isDiff = List.exists (fun el -> (snd(el)) = true) newPair in
    let newCtx = List.map (fun el -> fst(el)) newPair in
    olCtx.OlContext.lst <- newCtx;
    isDiff
    
  let solveUnion olPt c1 c2 c3 =
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let lctx = olCtx.OlContext.lst in
    let newCtx = [] in
    let newCtxRef = ref newCtx in
    newCtxRef := lctx;
    let boolList = List.map (fun (olc, f) ->
      newCtxRef := List.map (fun (olc', f') ->
      if (olc' = (fst(c3))) then (("#", 0), [])
      else (olc', f')) !newCtxRef;
      if (olc = (fst(c3))) then
	begin
	  newCtxRef := c1 :: c2 :: !newCtxRef;
	  true
        end
      else false
    ) lctx in
    let isDiff = List.exists (fun el -> el = true) boolList in
    olCtx.OlContext.lst <- !newCtxRef;
    isDiff
    
  let solveIn olPt c t = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let newPair = List.map (fun (olc, f) ->  
      if olc = c then
      (* Hack to don't process formulas with the predicate EXISTS *)
      match t with
	| EXISTS (s, i, t) -> ((olc, f), false)
	| _ -> if (List.exists (fun el -> el = t) f) then ((olc, f), false)
	else ((olc, t :: f), true)
      else ((olc, f), false)
    ) olCtx.OlContext.lst in
    let isDiff = List.exists (fun el -> (snd(el)) = true) newPair in
    let newCtx = List.map (fun el -> fst(el)) newPair in
    olCtx.OlContext.lst <- newCtx;
    isDiff
 
  let rewSeqFst seq cstr = 
    match cstr with 
    | ELIN (t, c) -> solveElin seq (OlContext.fixContext c) t
    | EMP (c) -> solveEmp seq (OlContext.fixContext c)
    | UNION (c1, c2, c3) ->
	let c3' = OlContext.fixContext c3 in
	let c2' = OlContext.fixContext c2 in
	let c1' = OlContext.fixContext c1 in
	solveUnion seq (c1', []) (c2', []) (c3', [])
    (* Any other constraint is despised *)
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
    
    let applyConstraints pt model = 
    while (List.exists (fun el -> (solveConstraintsFst el pt) = true) model.lst) do
      List.iter (fun cstr -> if solveConstraintsFst cstr pt then () else ()) model.lst
    done
   
  (* First phase: #bipole *)
  let solveFirstPhaseBpl olBipole =
    List.iter (fun (olProofTree, model) ->
      applyConstraints olProofTree model;
    ) olBipole
    
  (* First phase: #permute *)
  let solveFirstPhasePer pairOfBipoles =
    List.iter (fun ((olProofTree1, model1), (olProofTree2, model2)) ->
      applyConstraints olProofTree1 model1;
      applyConstraints olProofTree2 model2;
    ) pairOfBipoles
    
  let rewSeqSnd seq cstr = 
    match cstr with 
    | IN (t, c) -> solveIn seq (OlContext.fixContext c) t
    (* Any other constraint is despised *)
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
    
  let applyConstraints' pt model = 
    while (List.exists (fun el -> (solveConstraintsSnd el pt) = true) model.lst) do
      List.iter (fun cstr -> if solveConstraintsSnd cstr pt then () else ()) model.lst
    done    
    
  (* Second phase: #bipole *)     
  let solveSndPhaseBpl olBipole =
    List.iter (fun (olProofTree, model) ->
      applyConstraints' olProofTree model;
    ) olBipole
    
  (* Second phase: #permute *)     
  let solveSndPhasePer pairOfBipoles =
    List.iter (fun ((olProofTree1, model1), (olProofTree2, model2)) ->
      applyConstraints' olProofTree1 model1;
      applyConstraints' olProofTree2 model2;
    ) pairOfBipoles
    
  (*(* Third phase: Equating the contexts *)
  
  (* Verify the algorithm below :| *)
  let sameContexts ctx1 ctx2 = 
    List.for_all (fun (olc, f) ->
      List.exists (fun (olc', f') -> olc = olc') ctx2.OlContext.lst
    ) ctx1.OlContext.lst
    
    let getValidCtx ctx = 
    List.concat (List.map (fun ((s, i), f) -> if (String.get s 0) = '#' then [] else [(s, i)]) ctx.OlContext.lst)
    
  let getMaxPair n = 
    let rec max_value lst = match lst with
      | [] -> 0
      | hd :: tl -> max hd (max_value tl) in
    (* This will work just with one context *) 
    let str = fst(List.hd n) in
    let lst' = List.map (fun (s, i) -> i) n in (str, max_value lst')
  
  let createContextList m n maxPair =
    let i = ref (snd(maxPair)) in
    let counter = (fun () -> i := !i+1; !i) in
    List.map (fun (s, i) -> List.map (fun (s', i') -> (fst(maxPair), counter())) m) n
    
  let getContextForm ctx = 
    let lctx = List.fold_right (fun ((s,i), f) acc -> f @ acc) ctx.OlContext.lst [] in
    (("#", 0), lctx)
    
  (* Returns a (ctx, list of ctx) list *)
  let getAssocN n lst = 
    let j = ref (-1) in
    let counter = (fun () -> j := !j+1; !j) in
    List.map (fun (s, i) -> 
      ((s,i), (List.nth lst (counter())))
    ) n
  
  (* Returns a (ctx, list of ctx) list *)
  let getAssocM m lst = 
    let reagroupContextList lst = 
      let j = ref (-1) in
      let counter' = (fun () -> j := !j+1; !j) in
      List.map (fun lst' -> List.map (fun ctx -> List.nth lst' (counter'())) lst' ) lst in
    let k = ref (-1) in
    let counter = (fun () -> k := !k+1; !k) in
    let lst' = reagroupContextList lst in
    List.map (fun (s, i) -> ((s, i), List.nth lst (counter()))) m
  
  (* nCtx = (Ctx to find, List to rewrite the Ctx) *)
  let rewriteTree pt nctx = 
    let solve olPt ctx listOfCtx =
      let olSeq = OlProofTree.getConclusion olPt in
      let olCtx = OlSequent.getContext olSeq in
      let lctx = olCtx.OlContext.lst in
      let newCtxRef = ref [] in
      (*let ctxRemainder = ref [] in*)
      newCtxRef := lctx;
      List.iter (fun (olc, f) ->
	newCtxRef := List.map (fun (olc', f') ->
	if (olc' = ctx) then 
	  begin
	    (*ctxRemainder := (getContextForm (olc', f')) :: !ctxRemainder;*)  
	    (("#", 0), f')
	  end
	else (olc', f')) !newCtxRef;
	if (olc = ctx) then newCtxRef := listOfCtx @ !newCtxRef
	else ()
      ) lctx;
      (*newCtxRef := !ctxRemainder @ !newCtxRef;*)
      olCtx.OlContext.lst <- !newCtxRef in
    let rec rewTree olTree = 
      solve olTree (fst(nctx)) (snd(nctx));
      List.iter rewTree olTree.OlProofTree.tree in
    rewTree pt
    
  let fixContexts lst = 
    List.map (fun (s, i) -> ((s,i), [])) lst
      
  (* Create new contexts and apply this to ALL the tree *)
  (* seq1 is the conclusion and seq2 the premise *)
  let applyNewContexts pt seq1 seq2 = 
    let ctx1 = OlSequent.getContext seq1 in
    let ctx2 = OlSequent.getContext seq2 in
    let m = getValidCtx ctx1 in
    let n = getValidCtx ctx2 in
    let maxPair = getMaxPair n in
    let lst = createContextList m n maxPair in
    let nList = fixContexts (getAssocN n lst) in
    let mList = fixContexts (getAssocM m lst) in
    List.iter (fun nctx -> rewriteTree pt nctx) nList;
    List.iter (fun nctx -> rewriteTree pt nctx) mList;
    ()
  
  (* Get the sequents to rewrite the contexts to obtain an equality *)  
  let equatingContexts pt = 
    let ptRef = ref pt in
    let rec getSequents' pt = 
      if (List.exists (fun pt' ->
	match pt'.OlProofTree.rule with
	| SOME(r) -> false
	| NONE -> if (List.length pt'.OlProofTree.tree) = 0 then true else false
      ) pt.OlProofTree.tree) then
	if (sameContexts (OlProofTree.getContextFromPt (List.find (fun pt' -> 
	pt'.OlProofTree.tree <> []) pt.OlProofTree.tree)) 
	(OlProofTree.getContextFromPt pt)) then 
	  getSequents' (List.find (fun pt' -> pt'.OlProofTree.tree <> []) pt.OlProofTree.tree)
	else begin applyNewContexts !ptRef (OlProofTree.getConclusion pt) (OlProofTree.getConclusion (List.find (fun pt' -> pt'.tree <> 0) pt.OlProofTree.tree)); [] end
      else List.concat (List.map (fun p -> getSequents' p) pt.OlProofTree.tree) in
    getSequents' pt*)

end;;
