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
    
  let printFormList f = List.fold_right (fun f' acc -> (Prints.termToTexString (Term.formatForm f')) ^ ", " ^ acc) f ""
  
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
  
(*  let toTexString seq index mainRule actualHeight = match seq.pol with
    | ASYN -> (OlContext.toTexString seq.ctx "lft" index mainRule actualHeight) ^ " \\Uparrow "
    | SYNC -> (OlContext.toTexString seq.ctx "lft" index mainRule actualHeight) ^ " \\Downarrow "*)

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
  let print_subexp (str, i) = print_string (str ^ (string_of_int i))
  
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
  print_endline "Hashtbl end"
  
  (*let rec rewriteContext c acc =
    let ctxList = Hashtbl.find subexpRewrite c in
    let (s, i) = c in
    if List.exists (fun ((s', i'), tlist) -> s = s' || i' = (-1)) ctxList then ctxList
    else List.concat (List.map (fun (olc, tList') -> rewriteContext olc ) ctxList)*)
    
  let applyCstrToHashtable cstr isOpenLeaf = 
    match cstr with 
    | EMP (c) -> let c' = (OlContext.fixSubLabel c) in
                 Hashtbl.iter (fun k oldRewrite -> 
                   let newRewrite = List.fold_right (fun (ctx, fList) acc ->
	             if ctx = c' then acc
	             else (ctx, fList) :: acc
	           ) oldRewrite [] in
	           Hashtbl.replace subexpRewrite k newRewrite
	         ) subexpRewrite
                   
    | IN (t, c) -> let c' = (OlContext.fixSubLabel c) in
                   Hashtbl.iter (fun k oldRewrite -> 
                     let formulaExists = List.exists (fun (ctx, tlist) -> 
		       List.exists (fun el -> el = t) tlist
	 	     ) oldRewrite in
	 	     if formulaExists then ()
	 	     else begin
                       let newRewrite = List.fold_right (fun (ctx, tlist) acc ->
	                 if ctx = c' then begin
	                   if isOpenLeaf then (ctx, t :: tlist) :: acc
	                   else ((fst(ctx), -1),  t :: tlist) :: acc
		         end else (ctx, tlist) :: acc
	               ) oldRewrite [] in
	               Hashtbl.replace subexpRewrite k newRewrite
	             end
	           ) subexpRewrite
	           
    | UNION (c1, c2, c3) -> let c3' = OlContext.fixSubLabel c3 in
			    let c2' = OlContext.fixSubLabel c2 in
		 	    let c1' = OlContext.fixSubLabel c1 in
		 	    Hashtbl.iter (fun k oldRewrite -> 
                              let newRewrite = List.fold_right (fun (ctx, tlist) acc ->
	                        if ctx = c3' then (c1', []) :: (c2', []) :: acc
		                else (ctx, tlist) :: acc
	                      ) oldRewrite [] in
	                      Hashtbl.replace subexpRewrite k newRewrite
	                    ) subexpRewrite
		 	    
    | MINUS (c1, t, c2) -> let c2' = OlContext.fixSubLabel c2 in
	                   let c1' = OlContext.fixSubLabel c1 in
	                   Hashtbl.iter (fun k oldRewrite -> 
                             let newRewrite = List.fold_right (fun (ctx, tlist) acc ->
	                       if ctx = c2' then begin
	                         let c1' = Hashtbl.find subexpRewrite c1 in
	                         let newRewrite = (List.map (fun (ctx', tlist') -> 
	                           (ctx', (List.fold_right (fun el acc' -> 
	                             if el = t then acc'
	                             else el :: acc'
	                           ) tlist' []))
	                         ) c1' ) in newRewrite @ acc
                               end else (ctx, tlist) :: acc
	                     ) oldRewrite [] in
	                     Hashtbl.replace subexpRewrite k newRewrite
	                   ) subexpRewrite
  
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
    
  (* UNION(Γ1, Γ2, Γ3): Γ3 → Γ1, Γ2 *)
    (*let solveUnion seq c1 c2 cU =
    let olCtx = OlSequent.getContext seq in
    let isDifferent = ref false in
    let newCtx = List.fold_left (fun acc (olc, f') ->
		  if (olc = cU) then begin
		    Hashtbl.add subexpRewrite olc ([(c1, []);(c2, [])]);
		    isDifferent := true; (c1, []) :: (c2, []) :: acc
		  end else (olc, f') :: acc
		 ) [] olCtx.OlContext.lst in
    olCtx.OlContext.lst <- newCtx; !isDifferent*)
  
  let solveUnion seq c1 c2 cU =
    let olCtx = OlSequent.getContext seq in
    let isDifferent = ref false in
    List.iter (fun (olc, f') ->
		  if (olc = cU) then begin
		    Hashtbl.add subexpRewrite olc ([(c1, []);(c2, [])]);
		    isDifferent := true;
		  end else ()
    ) olCtx.OlContext.lst;
    !isDifferent
    
  (* IN (F, Γ): Γ → Γ, F (if the sequent is an open leaf) *)
  (*            Γ → F    (else)                            *)

  let solveIn seq c t isOpenLeaf =
    let olCtx = OlSequent.getContext seq in
    let isDifferent = ref false in
    List.iter (fun (olc, f) ->  
      if olc = c then begin
	(* Don't process formulas with the predicate EXISTS *)
	match t with
	  | EXISTS (s, i, t) -> ()
	  | _ -> begin
		   isDifferent := true;
		   if isOpenLeaf then begin 
		     let oldRewrite = try Hashtbl.find subexpRewrite olc with Not_found -> [] in
		     let newRewrite = if Hashtbl.mem subexpRewrite olc then
		       List.fold_right (fun (c, tlist) acc ->
		         if olc = c then (c, t :: tlist) :: acc
		         else (c, tlist) :: acc
		       ) oldRewrite [] else (oldRewrite @ [(c, [t])]) in
		     Hashtbl.replace subexpRewrite olc newRewrite
		   end else begin
		     let oldRewrite = try Hashtbl.find subexpRewrite olc with Not_found -> [] in
		     Hashtbl.replace subexpRewrite olc ([((fst(olc), -1), [t])] @ oldRewrite)
		   end
		 end
	end else ()
    ) olCtx.OlContext.lst;
    !isDifferent
    
  (* MINUS (Γ0, F, Γ1): Γ1 → Γ0 - F *)
  let solveMinus seq c1 t c2 =
    let olCtx = OlSequent.getContext seq in
    let isDifferent = ref false in
    List.iter (fun (olc, f) ->
      if olc = c2 then begin
	let l1 = Hashtbl.find subexpRewrite c1 in
	let newRewrite = (List.map (fun (olc', f') -> 
	  (olc', (List.fold_right (fun el acc' -> 
	    if el = t then begin isDifferent := true; acc'
	    end else el :: acc'
	  ) f' []))
	) l1) in
	Hashtbl.add subexpRewrite olc newRewrite;
      end else ()
    ) olCtx.OlContext.lst;
    !isDifferent
 
 (* isOpenLeaf is a boolean that it's necessary because the constraint IN (G, F) *)
 (* application differs according to that.                                       *)
  let rewriteSequent olTree model isOpenLeaf =
    let seq = OlProofTree.getConclusion olTree in
    let applyConstraint seq cstr = 
      match cstr with 
      | EMP (c) -> solveEmp seq (OlContext.fixSubLabel c)
      | IN (t, c) -> solveIn seq (OlContext.fixSubLabel c) t isOpenLeaf
      | UNION (c1, c2, c3) ->
			  let c3' = OlContext.fixSubLabel c3 in
			  let c2' = OlContext.fixSubLabel c2 in
			  let c1' = OlContext.fixSubLabel c1 in
			  solveUnion seq c1' c2' c3'
      | MINUS (c1, t, c2) -> 
			  let c2' = OlContext.fixSubLabel c2 in
			  let c1' = OlContext.fixSubLabel c1 in
			  solveMinus seq c1' t c2'
      (* Any other constraint is despised *)
      | _ -> false in
    (*while (List.exists (fun cstr -> (applyConstraint seq cstr) = true) model.lst) do () done*)
    let newModel = List.fold_left (fun acc cstr -> 
      if (applyConstraint seq cstr) then begin
	applyCstrToHashtable cstr isOpenLeaf;
        print_string "APPLIED: ";
        print_endline (Constraints.predToString cstr);
        print_hashtbl ();
        acc
      end else acc @ [cstr]
    ) [] model.lst in
    model.lst <- newModel; model
    
  (* The constraints are applied from the proof tree leafs to the root. *)
    
  (*let applyModel pt model = 
     let rec orderSequents olTree =
	if (olTree.OlProofTree.premises != []) then begin
	  let lst = List.concat (List.map orderSequents olTree.OlProofTree.premises) in 
	  lst @ [(olTree, false)]
        end else begin
	  let isOpenLeaf = match olTree.rule with
		       | Some(r) -> false
		       | None -> true 
	  in [(olTree, isOpenLeaf)]
	end in
      let orderedSequents = orderSequents pt in
      let model' = ref model in
      List.iter (fun (seq, isOpenLeaf) -> print_endline ("NOVO SEQUENTE"); model' := (rewriteSequent seq !model' isOpenLeaf)) orderedSequents;
      Hashtbl.reset subexpRewrite*)
      
   let applyModel pt model = 
     let model' = ref model in
     let rec applyModel' olTree =
	if (olTree.OlProofTree.premises <> []) then begin
	  List.iter applyModel' olTree.OlProofTree.premises; 
	  model' := (rewriteSequent olTree !model' false)
        end else begin
	  let isOpenLeaf = match olTree.rule with
		       | Some(r) -> false
		       | None -> true 
	  in model' := (rewriteSequent olTree !model' isOpenLeaf)
	end in
    let rewriteSeq' seq = 
      let olCtx = OlSequent.getContext seq in
      let newCtx = List.fold_right (fun (olc, f) acc ->
        if Hashtbl.mem subexpRewrite olc then
          let ctxRewritten = Hashtbl.find subexpRewrite olc in
          if (List.exists (fun (olc', f') -> olc = olc') ctxRewritten) then (olc, f) :: acc
          else (List.map (fun (olc', f') -> (olc', [])) ctxRewritten) @ acc 
        else (olc, f) :: acc
      ) olCtx.OlContext.lst [] in
      let isDifferent = olCtx.OlContext.lst <> newCtx in
      olCtx.OlContext.lst <- newCtx; isDifferent in
    let rewriteSeq seq = 
      let olCtx = OlSequent.getContext seq in
      let newCtx = List.fold_right (fun (olc, f) acc ->
        if Hashtbl.mem subexpRewrite olc then
          let ctxRewritten = Hashtbl.find subexpRewrite olc in
          ctxRewritten @ [((fst(olc), -1), f)] @ acc
        else (olc, f) :: acc
      ) olCtx.OlContext.lst [] in
      olCtx.OlContext.lst <- newCtx in
    let rec rewriteTree olTree =
      List.iter rewriteTree olTree.OlProofTree.premises;
      (*while*) rewriteSeq olTree.OlProofTree.conclusion; (*do () done*)
      while rewriteSeq' olTree.OlProofTree.conclusion do () done in
    applyModel' pt;
    rewriteTree pt;
    print_endline ("NOVO SEQUENTE");
    Hashtbl.reset subexpRewrite
      
  (*let applyConstraints pt model = 
    while (List.exists (fun cstr -> (applyConstraint cstr pt) = true) model.lst) do
      List.iter (fun cstr -> if applyConstraint cstr pt then () else ()) model.lst
    done*)
   
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