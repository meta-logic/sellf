(****************************************************)
(*                                                  *)
(*  Leonardo Lima, 2013                             *)
(*                                                  *)
(*  Implements the Object Logic (OL), solving the   *)
(*  constraints and making each sequent readable.   *)
(*                                                  *)
(****************************************************)

(* Suggestion: Change the name of these modules to viewer as in the Model-Viewer-Controller design pattern. *)

open Constraints 
open ContextSchema
open Llrules
open ProofTreeSchema 
open Sequent
open Types
open Subexponentials

module type OLCONTEXT =
  sig
  
    type subexp = string * int
    type ctx = subexp * terms list
    type context = { mutable lst : ctx list  }
    val create : subexp list -> context
    val remFirstChar : string -> string
    val getSubLabels : context -> string list
    val toStringForms : terms list -> string -> string -> int -> string -> string
    val toTexString : context -> string -> int -> string -> int -> string
    val fixSubLabel : subexp -> subexp
  
  end

module OlContext : OLCONTEXT = struct

  type subexp = string * int
  
  type ctx = subexp * terms list
  
  type context = {
    mutable lst : ctx list;
  }
  
  let create ctxList = {
    lst = List.map (fun ctx -> (ctx, [])) ctxList;
  }
  
  (* Some subexponentials labels comes with '#' or '$' as first character.*)
  (* For comparison reasons, we need to take away these characters.       *)
  let remFirstChar subLabel = 
    if (String.get subLabel 0) = '#' || (String.get subLabel 0) = '$' then 
      try String.sub subLabel 1 ((String.length subLabel)-1) 
      with Invalid_argument("index out of bounds") -> subLabel
    else subLabel
    
  let remComma str = try String.sub str 0 ((String.length str) - 2) 
		     with Invalid_argument("String.sub") -> str
  
  (* To print the formulas colorized properly, we need to know the height *)
  (* of the proof tree. TODO: Analyze the necessity of mod operation here.*)
  let colorizeForm f actualHeight =
    match (actualHeight mod 2) with
    | 0 -> "{\color{red}" ^ (Prints.termToTexString (Term.formatForm f)) ^ "}"
    | 1 -> "{\color{blue}" ^ (Prints.termToTexString (Term.formatForm f)) ^ "}"
  
  (* Collects a set of subexponential labels, eliminating the repetitions *)
  (* and the invalid labels as '#'.                                       *)
  let getSubLabels ctx =
    List.fold_right (fun ((label, index), f) acc ->  
      if (List.exists (fun el -> el = (remFirstChar label)) acc) || label = "#" then acc
      else (remFirstChar label) :: acc
    ) ctx.lst []
    
  (* Prints context variables, considering the right side and generates   *)
  (* new contexts if connectives are declared.                            *)
  let toStringVariable subLabel index maxIndex side = 
    let k = ref maxIndex in
    let generateIndex = (fun () -> k := !k+1; !k) in
    let conList = try Hashtbl.find Subexponentials.conTbl subLabel with Not_found -> [] in
    match (conList, side) with
    | ([], "lft") -> let (arity, side) = Hashtbl.find Subexponentials.ctxTbl subLabel in
		     if arity = MANY then "\\Gamma_{" ^ (Prints.remSpecial subLabel) ^ "}^{" ^ (string_of_int index) ^ "}, "
		     else "C^{" ^ (string_of_int index) ^ "}_{" ^ (Prints.remSpecial subLabel) ^ "}, "
    | ([], "rght") -> let (arity, side) = Hashtbl.find Subexponentials.ctxTbl subLabel in
		      if arity = MANY then "\\Delta_{" ^ (Prints.remSpecial subLabel) ^ "}^{" ^ (string_of_int index) ^ "}, "
		      else "C^{" ^ (string_of_int index) ^ "}_{" ^ (Prints.remSpecial subLabel) ^ "}, "
    | (lst, "lft") -> List.fold_right (fun con acc -> 
			let conTex = try Hashtbl.find Subexponentials.conTexTbl con with Not_found -> failwith ("The LaTeX code of the connective " ^ con ^ " was not found. Please verify the specification file.") in 
			conTex ^ "\\Gamma_{" ^ (Prints.remSpecial subLabel) ^ "}^{" ^ (string_of_int(generateIndex())) ^ "}, " ^ acc
		      ) lst ""
    | (lst, "rght") -> List.fold_right (fun con acc -> 
			let conTex = try Hashtbl.find Subexponentials.conTexTbl con with Not_found -> failwith ("The LaTeX code of the connective " ^ con ^ " was not found. Please verify the specification file.") in 
			conTex ^ "\\Delta_{" ^ (Prints.remSpecial subLabel) ^ "}^{" ^ (string_of_int(generateIndex())) ^ "}, " ^ acc
		      ) lst ""
    | _ -> failwith ("Error: the subexponential " ^ subLabel ^ " can not be printed.")

  (* Prints formula variables, considering the right side and colorize the*)
  (* formula if it corresponds to the rule that will be applied. If a for-*)
  (* mula appears in a wrong context, a warning will be printed.          *)
  let toStringForms formulas side subLabel actualHeight mainRule = 
    (List.fold_right (fun f acc ->
      let formSide = Specification.getSide (Specification.getPred f) in
      let sameSide = Subexponentials.isSameSide subLabel formSide in
      match sameSide with
      | true -> if formSide = side then begin
		  let rule = Prints.termToTexString (Term.formatForm (f)) in
		  if rule = mainRule then (colorizeForm f actualHeight) ^ ", " ^ acc
		  else (Prints.termToTexString (Term.formatForm f)) ^ ", " ^ acc end
		else acc
      | false -> begin print_string ("\nWarning: the following formula can't belong to the context "
		^ subLabel ^ ": " ^ (Prints.termToString f) ^ "\nPlease verify your especification.\n"); acc end
    ) formulas "")
  
  let toTexString ctx side maxIndex mainRule actualHeight = 
    let subLst = Subexponentials.getAllValid () in
    let slotToTex ctx side sub actualHeight =
    (* Prints context variables *)
    (List.fold_right (fun ((n, i), f) acc ->
      let correctSide = ((n = sub) && (Subexponentials.isSameSide n side)) in
      match (f, correctSide, i) with
      | (_, _, -1) -> acc
      | ([], true, _) -> (toStringVariable n i maxIndex side) ^ acc
      | (f', true, _) -> (toStringVariable n i maxIndex side) ^ (toStringForms f' side n actualHeight mainRule) ^ acc
      | _ -> acc
    ) ctx.lst "") ^
    (* Prints formula variables *)
    (List.fold_right (fun ((n, i), f) acc ->
      let correctSide = ((n = sub) && (Subexponentials.isSameSide n side)) in
      match (side, correctSide, i) with
      | ("lft", true, -1)  -> (toStringForms f "lft" (remFirstChar n) actualHeight mainRule) ^ acc
      | ("rght", true, -1) -> (toStringForms f "rght" (remFirstChar n) actualHeight mainRule) ^ acc
      | _ -> acc
    ) ctx.lst "") in
    (* Prints all the slots *)
    let slotString = List.fold_right (fun sub acc ->
      match Subexponentials.isSameSide sub side with
        | false -> acc
        | true ->
          match remComma (slotToTex ctx side sub actualHeight) with
            | "" -> begin match acc with
              (*| "" -> " \\cdot " ^ acc*)
              | _ -> "; {}\cdot{} " ^ acc
            end
            | str -> begin match acc with
              (*| "" -> str ^ " " ^ acc*)
              | _ -> ";{} " ^ str ^ acc
            end
    ) subLst "" in
    String.sub slotString 1 ((String.length slotString) - 1)
  
  (* Hack to fix the name of subexponential that come without $ *)
  let fixSubLabel ctx =
    if (fst(ctx) = "gamma" || fst(ctx) = "infty") then (("$" ^ (fst(ctx))), snd(ctx))
    else ctx
  
end;;

module type OLSEQUENT =
  sig

    type sequent = {
      mutable ctx : OlContext.context;
      goals : terms list;
      mutable pol : phase }  
    val create : OlContext.context -> terms list -> phase -> sequent 
    val getContext : sequent -> OlContext.context
    val getMainForm : sequent -> terms
    val toTexString : sequent -> int -> string -> int -> string
  
  end

module OlSequent : OLSEQUENT = struct
  
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
  
  let getMainForm seq = match seq.goals with
    | [] -> failwith "Sequent has no goals."
    | _ -> Term.getOnlyRule (Term.formatForm (List.hd seq.goals))
  
  let toTexString seq index mainRule actualHeight = 
    (OlContext.toTexString seq.ctx "lft" index mainRule actualHeight) ^ " \\vdash " ^ (OlContext.toTexString seq.ctx "rght" index mainRule actualHeight)

end;;

module type OLPROOFTREE =
  sig

    type prooftree = {
      mutable conclusion : OlSequent.sequent;
      mutable premises : prooftree list;
      mutable rule : llrule option}
    
    val create : OlSequent.sequent -> llrule option -> prooftree
    val getConclusion : prooftree -> OlSequent.sequent
    val getContextFromPt : prooftree -> OlContext.context
    val toPermutationFormat : prooftree -> unit
    val toTexString : prooftree -> string
    val toMacroRule : prooftree -> unit
  
  end

module OlProofTree : OLPROOFTREE = struct
  
  type prooftree = {
    mutable conclusion : OlSequent.sequent;
    mutable premises : prooftree list;
    mutable rule : llrule option
  }
  
  let create sq rl = {
    conclusion = sq;
    premises = [];
    rule = rl;
  }

  let getConclusion pt = pt.conclusion
  
  let getContextFromPt pt = OlSequent.getContext (getConclusion pt) 
  
  let getRule pt = pt.rule
  
  let actualHeight = ref (-1)
  
  let counter () = if (!actualHeight + 1) > 1 then actualHeight := 0 else actualHeight := !actualHeight + 1; !actualHeight
  
  let getPol pt = 
    let conclusion = getConclusion pt in
    conclusion.OlSequent.pol

  let toPermutationFormat olPt = 
    let firstPt = List.hd olPt.premises in
    let rec getSeq' pt = 
      match (pt.premises, getPol pt) with 
      | ([], ASYN) -> 
				begin
				  match pt.rule with 
				  | Some(r) -> []
				  | None -> [pt]
				end
      | (lpt, _) -> List.concat (List.map (fun p -> getSeq' p) lpt) 
    in      
    let rec getSeq pt =
        match pt.premises with
        | [] -> 
          begin
            match (getRule pt) with 
            | Some(r) -> []
            | None -> [pt]
          end
        | _ -> begin match (getPol pt) with
 	 		    | ASYN ->
 	 		      if (List.exists (fun el -> (getPol el) = SYNC) pt.premises) then
 	 		        let nextPt = List.find (fun el -> (getPol el) = SYNC) pt.premises in
              nextPt.premises <- getSeq' nextPt;
 	 		        [nextPt]
 	 		      else List.concat (List.map (fun p -> getSeq p) pt.premises)
 	 		    | SYNC -> 
 	 		      List.concat (List.map (fun p -> getSeq p) pt.premises)
 	 		    end 
    in  
    let newPtList = getSeq firstPt in
    olPt.premises <- newPtList;
    olPt.conclusion <- firstPt.conclusion
    
  let toMacroRule olPt =
    let firstPt = List.hd olPt.premises in
    let rec getOpenLeaves pt = 
      match pt.rule with
      | Some(rule) -> List.concat (List.map (fun p -> getOpenLeaves p) pt.premises)
      | None -> [pt] in
    let newPremises = getOpenLeaves olPt in
    olPt.conclusion <- firstPt.conclusion;
    olPt.premises <- newPremises
   
  let sideToChar side = 
    match side with
    | "rght" -> "R"
    | "lft" -> "L"
    | _ -> ""
    
  let maxIndex pt = 
    let index = ref (-1) in
    let rec getSeq pt = 
      match pt.rule with
      | Some(rule) -> if pt.premises = [] then [pt] else List.concat (List.map (fun p -> getSeq p) pt.premises)
      | None -> [pt] in
    let olPt = List.hd (getSeq pt) in
    let olSeq = getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    List.iter (fun ((s, i), l) -> if i > !index then index := i else ()) olCtx.OlContext.lst;
    !index
    
  let toTexString pt =
    let index = maxIndex pt in
    let rec toTexString' pt level = 
      match pt.rule with
      | Some(r) ->
	      let seq = getConclusion pt in
	      let rule = OlSequent.getMainForm seq in
	      let mainRule = Term.formatForm (List.hd seq.OlSequent.goals) in
	      let topproof = match pt.premises with
	        | [] -> ""
	        | hd::tl -> (toTexString' hd (level + 1))^(List.fold_right (fun el acc -> "\n\\quad\n"^(toTexString' el (level + 1))) tl "") 
	      in
        let pred = List.hd seq.OlSequent.goals in
        let formSide = Specification.getSide (Specification.getPred pred) in
        let ruleNameTex = (Prints.termToTexString rule) ^ "_{" ^ (sideToChar formSide) ^ "}" in
	      (*"\\infer[" ^ ruleNameTex ^ "]{" ^ (OlSequent.toTexString (getConclusion pt)) ^ "}\n{" ^ topproof ^ "}"*)
	      "\\cfrac{" ^ topproof ^ "}\n{" ^ (OlSequent.toTexString (getConclusion pt) index (Prints.termToTexString mainRule) level) ^ "} \\;\\; " ^ ruleNameTex 
      | None -> (OlSequent.toTexString (getConclusion pt) index "#" level) 
    in
    toTexString' pt 0

end;;

module type DERIVATION = 
  sig
  
    type bipole = ProofTreeSchema.prooftree * Constraints.constraintset
    type olBipole = OlProofTree.prooftree * Constraints.constraintset
    val remakeBipoles : bipole list -> olBipole list
    val remakePermutation : (bipole * bipole) list -> (olBipole * olBipole) list
    val solveFirstPhaseBpl : olBipole list -> unit
    val solveFirstPhasePer : (olBipole * olBipole) list -> unit
    val solveSndPhaseBpl : olBipole list -> unit
    val solveSndPhasePer : (olBipole * olBipole) list -> unit
    val equatingContexts : OlProofTree.prooftree -> unit  
  
  end

module Derivation : DERIVATION = struct

  type bipole = ProofTreeSchema.prooftree * Constraints.constraintset
  
  type olBipole = OlProofTree.prooftree * Constraints.constraintset

  let rec remakeTree pt =
    let seq = ProofTreeSchema.getConclusion pt in
    let rule = ProofTreeSchema.getRule pt in
    let ctx = SequentSchema.getContext seq in
    let ctxListRef = Hashtbl.fold (fun str1 int1 acc -> 
      if str1 = "$gamma" || str1 = "$infty" then acc
      else (str1, int1) :: acc
    ) ctx.ContextSchema.hash [] in
    let context = OlContext.create ctxListRef in
    let goals = SequentSchema.getGoals seq in
    let polarity = SequentSchema.getPhase seq in
    let sequent = OlSequent.create context goals polarity in
    let olPt = OlProofTree.create sequent rule in
    if pt.ProofTreeSchema.premises = [] then olPt else
    begin 
      olPt.OlProofTree.premises <- List.map remakeTree pt.ProofTreeSchema.premises;
      olPt
    end 
    
  let remakeBipoles bplLst = 
    List.map (fun (pt, model) -> (remakeTree pt, model)) bplLst 
    
  let remakePermutation pair_bpl = 
    List.map (fun ((pt1, model1), (pt2, model2)) ->
      ((remakeTree pt1, model1), (remakeTree pt2, model2))) 
    pair_bpl
    
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

  let print_subexp (str, i) = print_endline (str ^ (string_of_int i))
    
  let solveElin olPt c t = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let bChange = ref false in
    let newCtx = (List.fold_left (fun acc (olc, f) ->  
      if olc = c then begin 
		      if snd(olc) = -1 then (olc, f) :: acc else
                      begin bChange := true; (((OlContext.remFirstChar (fst c)), -1), t :: f) :: acc end end
      else begin (olc, f) :: acc end
    ) [] olCtx.OlContext.lst) in
    olCtx.OlContext.lst <- newCtx; 
    !bChange
    
  let solveEmp olPt c = 
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let bChange = ref false in
    let newCtx = List.fold_left (fun acc (olc, f) ->
      if olc = c then begin bChange := true; acc end else (olc, f) :: acc)
      [] olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx; !bChange
    
  let solveUnion olPt c1 c2 cU =
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let lctx = olCtx.OlContext.lst in
    let bChange = ref false in
    let newCtx = List.fold_left (fun acc (olc', f') ->
		  if (olc' = cU) then 
		    begin bChange := true; (c1, []) :: (c2, []) :: acc end
		  else (olc', f') :: acc) [] lctx in
    olCtx.OlContext.lst <- newCtx; !bChange
    
let solveIn olPt c t =
    let olSeq = OlProofTree.getConclusion olPt in
    let olCtx = OlSequent.getContext olSeq in
    let bChange = ref false in
    let newCtx = List.map (fun (olc, f) ->  
      if olc = c then
      (* Hack to don't process formulas with the predicate EXISTS *)
      match t with
        | EXISTS (s, i, t) -> (olc, f)
        | _ -> if (List.exists (fun el -> el = t) f) then (olc, f)
        else begin bChange := true;
		     match Subexponentials.type_of (fst olc) with
					  | LIN | AFF -> 
		              (((OlContext.remFirstChar (fst c)), -1), t :: f)
					  | UNB | REL -> (olc, t :: f) 
		     end
      else (olc, f)
    ) olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx; !bChange
 
  let rewSeqFst seq cstr = 
    match cstr with 
    (*| ELIN (t, c) -> solveElin seq (OlContext.fixSubLabel c) t*)
    | EMP (c) -> solveEmp seq (OlContext.fixSubLabel c)
    | UNION (c1, c2, c3) ->
			let c3' = OlContext.fixSubLabel c3 in
			let c2' = OlContext.fixSubLabel c2 in
			let c1' = OlContext.fixSubLabel c1 in
			solveUnion seq c1' c2' c3'
    (* TODO add minus case *)
    (* Any other constraint is despised *)
    | _ -> false
    
  let solveConstraintsFst cstr olProofTree =
    match cstr with
    (*| ELIN (t, c) -> 
      let rec rewTreeElin olTree =
	rewSeqFst olTree cstr ::
	List.concat (List.map rewTreeElin olTree.OlProofTree.premises) in
      let boolList = rewTreeElin olProofTree in
      List.exists (fun el -> el = true) boolList*)
	
    | EMP (c) -> 
      let rec rewTreeEmp olTree =
	rewSeqFst olTree cstr ::
	List.concat (List.map rewTreeEmp olTree.OlProofTree.premises) in
      let boolList = rewTreeEmp olProofTree in
      List.exists (fun el -> el = true) boolList
      
    | UNION (c1, c2, c3) ->
      let rec rewTreeUnion olTree = 
	rewSeqFst olTree cstr ::
	List.concat (List.map rewTreeUnion olTree.OlProofTree.premises) in
      let boolList = rewTreeUnion olProofTree in
      List.exists (fun el -> el = true) boolList
      
    (* TODO add minus case *)
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
    | IN (t, c) -> solveIn seq (OlContext.fixSubLabel c) t
    (* Any other constraint is despised *)
    | _ -> false
    
  let solveConstraintsSnd cstr olProofTree =
    match cstr with
    | IN (t, c) -> 
      let rec rewTreeIn olTree = 
	rewSeqSnd olTree cstr ::
	List.concat (List.map rewTreeIn olTree.OlProofTree.premises) in
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
    
  (* Third phase: Equating the contexts *)
  
  let sameContexts ctx1 ctx2 str = 
    List.for_all (fun (olc, f) ->
      if (fst(olc)) = str then
	List.exists (fun (olc', f') -> (olc = olc')) ctx2.OlContext.lst
      else true
    ) ctx1.OlContext.lst
    
  let getValidCtx ctx str = 
    List.concat (List.map (fun ((s, i), f) -> 
    if ((String.get s 0) = '#') || s <> str then []
    else [(s, i)]) ctx.OlContext.lst)
    
  let getMaxPair (n: OlContext.subexp list) = 
    let rec max_value lst = match lst with
      | [] -> 0
      | hd :: tl -> max hd (max_value tl) in
    let str = fst(List.hd n) in
    let lst' = List.map (fun (s, i) -> i) n in (str, max_value lst')
  
  let createContextList (m: OlContext.subexp list) (n: OlContext.subexp list) (maxPair: OlContext.subexp) =
    let ctx_name = fst(maxPair) in
    let i = ref (snd(maxPair)) in
    let counter = (fun () -> i := !i+1; !i) in
    List.map (fun (s, i) -> List.map (fun (s', i') -> ctx_name, counter()) m) n
    
  (* Returns a (ctx, list of ctx) list *)
  let getAssocN n lst = 
    let j = ref (-1) in
    let counter = (fun () -> j := !j+1; !j) in
    List.map (fun (s, i) -> ((s,i), (List.nth lst (counter())))) n
  
  (* Returns a (ctx, list of ctx) list *)
  let getAssocM m lst = 
    let reagroupContextList lst = 
      let q = ref (-1) in
      let counter' = (fun () -> q := !q+1) in
      let head = List.hd lst in
      List.map (fun ctx ->
	counter'();
	List.fold_right (fun lst'' acc -> 
	  (List.nth lst'' !q) :: acc
	) lst []
      ) head in
    let k = ref (-1) in
    let counter = (fun () -> k := !k+1; !k) in
    let lst' = reagroupContextList lst in
    List.map (fun (s, i) -> ((s, i), List.nth lst' (counter()))) m
  
  (* nCtx = (Ctx to find, List to rewrite the Ctx) *)
  let rewriteTree pt nctx = 
    let solve olPt ctx listOfCtx =
      let olSeq = OlProofTree.getConclusion olPt in
      let olCtx = OlSequent.getContext olSeq in
      let lctx = olCtx.OlContext.lst in
      let newCtxRef = ref lctx in
      List.iter (fun (olc, f) ->
	newCtxRef := List.map (fun (olc', f') ->
	if (olc' = ctx) then (((fst(ctx)), -1), f')
	else (olc', f')) !newCtxRef;
	if (olc = ctx) then newCtxRef := listOfCtx @ !newCtxRef
	else ()
      ) lctx;
      olCtx.OlContext.lst <- !newCtxRef in
    let rec rewTree olTree = 
      solve olTree (fst(nctx)) (snd(nctx));
      List.iter rewTree olTree.OlProofTree.premises in
    rewTree pt
    
  let fixContexts lst = 
    List.map (fun lst' -> List.map (fun (s, i) -> ((s,i), [])) lst') lst
      
  (* Create new contexts and apply this to the tree *)
  (* seq1 is the conclusion and seq2 the premise *)
  let applyNewContexts pt seq1 seq2 str = 
    let ctx1 = OlSequent.getContext seq1 in
    let ctx2 = OlSequent.getContext seq2 in
    let m = getValidCtx ctx1 str in
    let n = getValidCtx ctx2 str in
    let maxPair = getMaxPair n in
    let lst = fixContexts (createContextList m n maxPair) in
    let nList = getAssocN n lst in
    let mList = getAssocM m lst in
    List.iter (fun nctx -> rewriteTree pt nctx) nList;
    List.iter (fun nctx -> rewriteTree pt nctx) mList;
    ()
  
  (* Get the sequents to rewrite the contexts to obtain an equality *)  
  let equatingContexts pt = 
    let ptRef = ref pt in
    let rec getSequents' pt = 
      if (List.exists (fun pt' ->
	  match pt'.OlProofTree.rule with
	  | Some(r) -> if (pt'.OlProofTree.premises = []) then true else false
	  | None -> false
	) pt.OlProofTree.premises) then
	begin
	  let pt2 = List.find (fun pt' -> pt'.OlProofTree.premises <> []) pt.OlProofTree.premises in
	  let ctx1 = (OlProofTree.getContextFromPt pt) in
	  let ctx2 = (OlProofTree.getContextFromPt pt2) in
	  let seq1 = OlProofTree.getConclusion pt in
	  let seq2 = OlProofTree.getConclusion pt2 in
	  let ctx_str_lst = OlContext.getSubLabels ctx1 in
	  if (List.for_all (fun str -> sameContexts ctx1 ctx2 str) ctx_str_lst) then
	    getSequents' pt2
	  else 
	    begin 
	      let ctx_str_lst = OlContext.getSubLabels ctx1 in
	      let diff_ctx = List.map (fun el -> (el, (sameContexts ctx1 ctx2 el))) ctx_str_lst in
	      List.iter (fun (str, bol) -> 
		if bol = false then
		while (sameContexts ctx1 ctx2 str) = false do
		  applyNewContexts !ptRef seq1 seq2 str
		done
	      ) diff_ctx
	    end
	end
      else List.iter (fun p -> getSequents' p) pt.OlProofTree.premises in
    getSequents' pt

end;;

(* TODO: make it more modular? *)
(* Discuss it with Leo. [Giselle]*)
let apply_permute perm_bipoles = begin
  let olPt = ref [] in
  olPt := Derivation.remakePermutation perm_bipoles;
  Derivation.solveFirstPhasePer !olPt;
  Derivation.solveSndPhasePer !olPt;
  List.iter (fun ((olt1, model1), (olt2, model2)) -> 
    Derivation.equatingContexts olt1;
    Derivation.equatingContexts olt2;
    OlProofTree.toPermutationFormat olt1;
    OlProofTree.toPermutationFormat olt2;
  ) !olPt;
  !olPt
end ;;

let apply_perm_not_found perm_not_found = begin
  let olPt = ref [] in
  olPt := Derivation.remakeBipoles perm_not_found;
  Derivation.solveFirstPhaseBpl !olPt;
  Derivation.solveSndPhaseBpl !olPt;
  !olPt
end ;;
