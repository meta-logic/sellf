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
    val toStringForms : terms list -> string -> string -> int -> terms -> string
    val toTexString : context -> string -> int -> terms -> int -> string
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
    | 0 -> "{\\color{red}" ^ (Prints.termToTexString (Specification.getObjectLogicMainFormula f)) ^ "}"
    | 1 -> "{\\color{blue}" ^ (Prints.termToTexString (Specification.getObjectLogicMainFormula f)) ^ "}"
    | _ -> failwith "Wrong result of module operation (colorizeForm)."
  
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
    | ([], "l") -> let (arity, side) = Hashtbl.find Subexponentials.ctxTbl subLabel in
		     if arity = MANY then "\\Gamma_{" ^ (Prints.remSpecial subLabel) ^ "}^{" ^ (string_of_int index) ^ "}, "
		     else "C^{" ^ (string_of_int index) ^ "}_{" ^ (Prints.remSpecial subLabel) ^ "}, "
    | ([], "r") -> let (arity, side) = Hashtbl.find Subexponentials.ctxTbl subLabel in
		      if arity = MANY then "\\Delta_{" ^ (Prints.remSpecial subLabel) ^ "}^{" ^ (string_of_int index) ^ "}, "
		      else "C^{" ^ (string_of_int index) ^ "}_{" ^ (Prints.remSpecial subLabel) ^ "}, "
    | (lst, "l") -> List.fold_right (fun con acc -> 
			let conTex = try Hashtbl.find Subexponentials.conTexTbl con with Not_found -> failwith ("The LaTeX code of the connective " ^ con ^ " was not found. Please verify the specification file.") in 
			conTex ^ "\\Gamma_{" ^ (Prints.remSpecial subLabel) ^ "}^{" ^ (string_of_int(generateIndex())) ^ "}, " ^ acc
		      ) lst ""
    | (lst, "r") -> List.fold_right (fun con acc -> 
			let conTex = try Hashtbl.find Subexponentials.conTexTbl con with Not_found -> failwith ("The LaTeX code of the connective " ^ con ^ " was not found. Please verify the specification file.") in 
			conTex ^ "\\Delta_{" ^ (Prints.remSpecial subLabel) ^ "}^{" ^ (string_of_int(generateIndex())) ^ "}, " ^ acc
		      ) lst ""
    | _ -> failwith ("Error: the subexponential " ^ subLabel ^ " can not be printed.")

  (* Prints formula variables, considering the right side and colorize the*)
  (* formula if it corresponds to the rule that will be applied. If a for-*)
  (* mula appears in a wrong context, a warning will be printed.          *)
  let toStringForms formulas side subLabel actualHeight mainRule = 
    (List.fold_right (fun f acc ->
      let formSide = Specification.getSide f in
      let sameSide = Subexponentials.isSameSide subLabel formSide in
      match sameSide with
      | true -> if formSide = side then begin
		  let rule = Specification.getObjectLogicMainFormula f in
		  if rule = mainRule then (colorizeForm f actualHeight) ^ ", " ^ acc
		  else (Prints.termToTexString (Specification.getObjectLogicMainFormula f)) ^ ", " ^ acc end
		else acc
      | false -> begin print_string ("\nWarning: the following formula can't belong to the context "
		^ subLabel ^ ": " ^ (Prints.termToString f) ^ "\nPlease verify your especification.\n"); acc end
    ) formulas "")
    
  let printFormList f = List.fold_right (fun f' acc -> (Prints.termToTexString (Specification.getHeadPredicate f')) ^ ", " ^ acc) f ""
  
  (* Subexponentials with index < 0 means that the context should not be *)
  (* writed, just the formulas.                                          *)
  let toTexString ctx side maxIndex mainRule actualHeight = 
    (*List.fold_right (fun ((n, i), f) acc -> "\\Gamma_{" ^ (remFirstChar n) ^ "}^{" ^ (string_of_int i) ^ "} ; " ^ (printFormList f) ^ acc) ctx.lst ""*)
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
      let correctSide = (((remFirstChar n) = sub) && (Subexponentials.isSameSide (remFirstChar n) side)) in
      match (side, correctSide, i) with
      | ("l", true, -1)  -> (toStringForms f "l" (remFirstChar n) actualHeight mainRule) ^ acc
      | ("r", true, -1) -> (toStringForms f "r" (remFirstChar n) actualHeight mainRule) ^ acc
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
              | _ -> "; {}\\cdot{} " ^ acc
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
    val toTexString : sequent -> int -> terms -> int -> string
  
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
  
  let toTexString seq index mainRule actualHeight = 
    (OlContext.toTexString seq.ctx "l" index mainRule actualHeight) ^ " \\vdash " ^ (OlContext.toTexString seq.ctx "r" index mainRule actualHeight)

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
	      let mainRule = Specification.getObjectLogicMainFormula (List.hd seq.OlSequent.goals) in
	      let topproof = match pt.premises with
	        | [] -> ""
	        | hd::tl -> (toTexString' hd (level + 1))^(List.fold_right (fun el acc -> "\n\\quad\n"^(toTexString' el (level + 1))) tl "") 
	      in
        let pred = List.hd seq.OlSequent.goals in
        let ruleNameTex = Specification.getRuleName pred in
	      (*"\\infer[" ^ ruleNameTex ^ "]{" ^ (OlSequent.toTexString (getConclusion pt)) ^ "}\n{" ^ topproof ^ "}"*)
	      "\\cfrac{" ^ topproof ^ "}\n{" ^ (OlSequent.toTexString (getConclusion pt) index mainRule level) ^ "} \\;\\; " ^ ruleNameTex 
      (* FIXME: using ZERO as a workaround... *)
      | None -> (OlSequent.toTexString (getConclusion pt) index ZERO level)
    in
    toTexString' pt 0

end;;

(* TODO: 
 * (1) refactor the methods so that they take only a bipole, and not a bipole list.
 * (2) do not transform the full tree into an olTree. With the new algorithm
 * this should no longer be necessary.
 *)
module type DERIVATION = 
  sig
  
    type bipole = ProofTreeSchema.prooftree * Constraints.constraintset
    type olBipole = OlProofTree.prooftree * Constraints.constraintset
    val remakeBipoles : bipole list -> olBipole list
    val remakePermutation : (bipole * bipole) list -> (olBipole * olBipole) list
    val rewriteBipoleList : olBipole list -> unit
    val rewritePermutationList : (olBipole * olBipole) list -> unit
  
  end

module Derivation : DERIVATION = struct

  (* Hashtable that contains the updates of subexponentials, to rewrite them properly. *)
  (* A context can be rewritten to other contexts and/or formulas.                     *)
  type ctx = string * int
  let subexpRewrite : (ctx, (ctx * terms list) list) Hashtbl.t = Hashtbl.create 100 ;;

  type bipole = ProofTreeSchema.prooftree * Constraints.constraintset
  
  type olBipole = OlProofTree.prooftree * Constraints.constraintset

  (* ProofTreeSchema and OlProofTree have different types, the first                   *)
  (* has sequents that have contexts of type ContextSchema, which consists of          *)
  (* a hashtable of (string * int). The latter has sequents that have contexts         *)
  (* of type OlContext, which contains a list of ((string * int) * list of formulas)   *)
  let rec remakeTree pt =
    let seq = ProofTreeSchema.getConclusion pt in
    let rule = ProofTreeSchema.getRule pt in
    let ctx = SequentSchema.getContext seq in
    let ctxListRef = Hashtbl.fold (fun str' int' acc -> 
      if str' = "$gamma" || str' = "$infty" then acc
      else (str', int') :: acc
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
    
  let remakeBipoles bpl_lst = 
    List.map (fun (pt, model) -> (remakeTree pt, model)) bpl_lst 
    
  let remakePermutation pair_bpl = 
    List.map (fun ((pt1, model1), (pt2, model2)) ->
      ((remakeTree pt1, model1), (remakeTree pt2, model2))) 
    pair_bpl 

  (* The functions below treat the constraints and their behavior. *)
  
  (*let print_subexp (str, i) = print_string (str ^ (string_of_int i))
  
  let print_hashtbl () = print_endline "Hashtbl begin: "; 
    Hashtbl.iter (fun k content -> 
      print_subexp k; 
      print_string " -> ";
      List.iter (fun (sub, f) -> print_subexp sub;
	print_string ", ";
	List.iter (fun t -> print_string ((Prints.termToTexString t) ^ ", ")) f;
	print_string " ^ "
      ) content;
      print_string " | "
    ) subexpRewrite; 
    print_string ("\n");
    print_endline "Hashtbl end"*)
  
  (*let rec rewriteContext c acc =
    let ctxList = Hashtbl.find subexpRewrite c in
    let (s, i) = c in
    if List.exists (fun ((s', i'), tlist) -> s = s' || i' = (-1)) ctxList then ctxList
    else List.concat (List.map (fun (olc, tList') -> rewriteContext olc ) ctxList)*)
 
  (* EMP (Γ): Γ → . *)
  let solveEmp seq c = 
    let olCtx = OlSequent.getContext seq in
    let isDifferent = ref false in
    List.iter (fun (olc, f) ->
		  if olc = c then begin
		    Hashtbl.replace subexpRewrite olc [];
		    isDifferent := true
		  end else ()
    ) olCtx.OlContext.lst;
    !isDifferent
    
  (* UNION(Γ1, Γ2, Γ3): Γ3 → Γ1, Γ2 only if Γ3 is bounded *)
  
  let solveUnion seq c1 c2 cU =
    let olCtx = OlSequent.getContext seq in
    let isDifferent = ref false in
    let isUnbounded = ref false in
    List.iter (fun (olc, f') ->
		  if (olc = cU) then begin
		    (match Subexponentials.type_of (fst olc) with
		     | LIN | AFF -> ()
		     | UNB | REL -> isUnbounded := true);
		     if !isUnbounded then ()
		     else begin
		       (* cU is replaced by the rewritten of c1 and c2 in the hashtable. *)
		       let c1' = Hashtbl.find subexpRewrite c1 in
		       let c2' = Hashtbl.find subexpRewrite c2 in
		       Hashtbl.add subexpRewrite olc (c1' @ c2');
		       isDifferent := true;
		     end
		  end else ()
    ) olCtx.OlContext.lst;
    !isDifferent
    
  (* IN (F, Γ): Γ → Γ, F (if the sequent is an open leaf) *)
  (*            Γ → F    (else)                            *)

  let solveIn seq c t isOpenLeaf isLeaf =
    let olCtx = OlSequent.getContext seq in
    let isDifferent = ref false in
    let isUnbounded = ref false in
    List.iter (fun (olc, f) ->  
      if olc = c && isLeaf then begin
	    (* Don't process formulas with the predicate EXISTS *)
	      match t with
	      | EXISTS (s, i, t) -> ()
	      | _ -> begin
		      isDifferent := true;
		      (match Subexponentials.type_of (fst olc) with
                                          | LIN | AFF -> ()
                                          | UNB | REL -> isUnbounded := true);
                      if !isUnbounded || (isLeaf && (not (isOpenLeaf))) then begin
			let oldRewrite = try Hashtbl.find subexpRewrite olc with Not_found -> [] in
			Hashtbl.replace subexpRewrite olc ([((fst(olc), -1), [t])] @ oldRewrite)
                      end else if isOpenLeaf then begin 
		        let oldRewrite = try Hashtbl.find subexpRewrite olc with Not_found -> [] in
			let newRewrite = if Hashtbl.mem subexpRewrite olc then
		        List.fold_right (fun (c, tlist) acc ->
			  if olc = c then (c, t :: tlist) :: acc
		          else (c, tlist) :: acc
		        ) oldRewrite [] else (oldRewrite @ [(c, [t])]) in
		        Hashtbl.replace subexpRewrite olc newRewrite
		      end else ()
		     end
      end else ()
    ) olCtx.OlContext.lst;
    !isDifferent
    
  (* MINUS (Γ0, F, Γ1): Γ1 → Γ0 - F *)
  let solveMinus seq c1 t c2 =
    let olCtx = OlSequent.getContext seq in
    let isDifferent = ref false in
    let isUnbounded = ref false in
    List.iter (fun (olc, f) ->
      if olc = c2 then begin
        (match Subexponentials.type_of (fst olc) with
           | LIN | AFF -> ()
           | UNB | REL -> isUnbounded := true);
        if !isUnbounded then ()
	else begin
	  let l1 = Hashtbl.find subexpRewrite c1 in
	  let newRewrite = (List.map (fun (olc', f') -> 
	    (olc', (List.fold_right (fun el acc' -> 
	      if el = t then begin isDifferent := true; acc'
	      end else el :: acc'
	     ) f' []))
	  ) l1) in
	  Hashtbl.add subexpRewrite olc newRewrite;
	end
      end else ()
    ) olCtx.OlContext.lst;
    !isDifferent
 
 (* isOpenLeaf and isLeaf are booleans that are necessary because the constraint *)
 (* IN (G, F) application differs according to that.                             *)
  let rewriteSequent olTree model isOpenLeaf isLeaf =
    let seq = OlProofTree.getConclusion olTree in
    let applyConstraint seq cstr = 
      match cstr with 
      | EMP (c) -> solveEmp seq (OlContext.fixSubLabel c)
      | IN (t, c) -> solveIn seq (OlContext.fixSubLabel c) t isOpenLeaf isLeaf
      | UNION (c1, c2, c3) ->
			  let c3' = OlContext.fixSubLabel c3 in
			  let c2' = OlContext.fixSubLabel c2 in
			  let c1' = OlContext.fixSubLabel c1 in
			  solveUnion seq c1' c2' c3'
      | SETMINUS (c1, t, c2) -> 
			  let c2' = OlContext.fixSubLabel c2 in
			  let c1' = OlContext.fixSubLabel c1 in
			  solveMinus seq c1' t c2'
      (* Any other constraint is despised *)
      | _ -> false in
    (* If a constraint is applied the new model doesn't contain it. *)
    let newModel = List.fold_left (fun acc cstr -> 
      if (applyConstraint seq cstr) then acc
      else acc @ [cstr]
    ) [] model.lst in
    model.lst <- newModel; model
      
  let applyModel pt model = 
    let model' = ref model in
    (* The constraints are applied from the proof tree leafs to the root *)
    let rec applyModel' olTree =
      if (olTree.OlProofTree.premises <> []) then begin
        List.iter applyModel' olTree.OlProofTree.premises; 
        model' := (rewriteSequent olTree !model' false false)
      end else begin
        let isLeaf = true in
        let isOpenLeaf = match olTree.rule with
          | Some(r) -> false
          | None -> true 
        in model' := (rewriteSequent olTree !model' isOpenLeaf isLeaf)
      end in
    (* Bounded case: if the context is member of the hashtable then replace with the rewritten. *)
    (* if not, do nothing.                                                                      *)
    let rewriteSeqBounded seq = 
      let olCtx = OlSequent.getContext seq in
      let newCtx = List.fold_right (fun (olc, f) acc ->
        if Hashtbl.mem subexpRewrite olc then begin
          let ctxRewritten = Hashtbl.find subexpRewrite olc in
          ctxRewritten @ acc
        end else (olc, f) :: acc
      ) olCtx.OlContext.lst [] in
      olCtx.OlContext.lst <- newCtx in
    (* Unbounded case: the new context list initiates with the context list of the end sequent. *)
    (* If the context is member of the hashtable, then replace with the rewritten               *)
    (* If not, despise the context.                                                             *)
    let rewriteSeqUnbounded endSeq seq = 
      let endSeqCtx = OlSequent.getContext endSeq in
      let olCtx = OlSequent.getContext seq in
      let newCtx = List.fold_right (fun (olc, f) acc ->
        if Hashtbl.mem subexpRewrite olc then begin
          let ctxRewritten = Hashtbl.find subexpRewrite olc in
          ctxRewritten @ acc
        end else acc
      ) olCtx.OlContext.lst endSeqCtx.lst in
      olCtx.OlContext.lst <- newCtx in
    (* Apply the rewritten in the hashtable on the proof tree *)
    let rec rewriteTree olTree endSeq isUnbounded =
      List.iter (fun el -> rewriteTree el endSeq isUnbounded) olTree.OlProofTree.premises;
      if isUnbounded then rewriteSeqUnbounded endSeq olTree.OlProofTree.conclusion
      else rewriteSeqBounded olTree.OlProofTree.conclusion in
    let olCtx = OlProofTree.getContextFromPt pt in
    let isUnbounded = match Subexponentials.type_of (fst(fst(List.hd olCtx.OlContext.lst))) with
           | LIN | AFF -> false
           | UNB | REL -> true in
    applyModel' pt;
    rewriteTree pt pt.OlProofTree.conclusion isUnbounded;
    Hashtbl.reset subexpRewrite
   
  let rewriteBipoleList olBipole =
    List.iter (fun (olProofTree, model) ->
      applyModel olProofTree model;
    ) olBipole

  let rewritePermutationList pairOfBipoles =
    List.iter (fun ((olProofTree1, model1), (olProofTree2, model2)) ->
      applyModel olProofTree1 model1;
      applyModel olProofTree2 model2;
    ) pairOfBipoles

end;;

(* TODO: make it more modular? *)
(* Discuss it with Leo. [Giselle]*)
let apply_permute perm_bipoles = begin
  let olPt = ref [] in
  olPt := Derivation.remakePermutation perm_bipoles;
  Derivation.rewritePermutationList !olPt;
  List.iter (fun ((olt1, model1), (olt2, model2)) -> 
    OlProofTree.toPermutationFormat olt1;
    OlProofTree.toPermutationFormat olt2;
  ) !olPt;
  !olPt
end ;;

let apply_perm_not_found perm_not_found = begin
  let olPt = ref [] in
  olPt := Derivation.remakeBipoles perm_not_found;
  Derivation.rewriteBipoleList !olPt;
  !olPt
end ;;
