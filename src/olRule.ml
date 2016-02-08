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
    val getSubLabels : context -> string list
    val toStringForms : terms list -> string -> string -> int -> terms -> string
    val toTexString : context -> string -> int -> terms -> int -> string
    val subToString : subexp -> string
  
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

  let remComma str = try String.sub str 0 ((String.length str) - 2) 
		                 with Invalid_argument(_) -> str

  let subToString (s, i) = s ^ "_" ^ string_of_int(i)
  
  (* To print the formulas colorized properly, we need to know the height *)
  (* of the proof tree. TODO: Analyze the necessity of mod operation here.*)
  let colorizeForm f currentHeight =
    match (currentHeight mod 2) with
    | 0 -> "{\\color{red}" ^ (Prints.termToTexString (Specification.getObjectLogicMainFormula f)) ^ "}"
    | 1 -> "{\\color{blue}" ^ (Prints.termToTexString (Specification.getObjectLogicMainFormula f)) ^ "}"
    | _ -> failwith "Wrong result of module operation (colorizeForm)."
  
  (* Collects a set of subexponential labels, eliminating the repetitions *)
  (* and the invalid labels as '#'.                                       *)
  let getSubLabels ctx =
    List.fold_right (fun ((label, index), f) acc ->  
      if (List.exists (fun el -> el = (Prints.remSpecial label)) acc) || label = "#" then acc
      else (Prints.remSpecial label) :: acc
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
		               else ""
    | ([], "r") -> let (arity, side) = Hashtbl.find Subexponentials.ctxTbl subLabel in
		               if arity = MANY then "\\Delta_{" ^ (Prints.remSpecial subLabel) ^ "}^{" ^ (string_of_int index) ^ "}, "
		               else ""
    | (lst, "l") -> List.fold_right (fun con acc -> 
			                               let conTex = try Hashtbl.find Subexponentials.conTexTbl con with Not_found ->
                                                    failwith ("The LaTeX code of the connective " ^ con ^ " was not found. Please verify the specification file.") in 
			                               conTex ^ "\\Gamma_{" ^ (Prints.remSpecial subLabel) ^ "}^{" ^ (string_of_int(generateIndex())) ^ "}, " ^ acc
		                                ) lst ""
    | (lst, "r") -> List.fold_right (fun con acc -> 
			                               let conTex = try Hashtbl.find Subexponentials.conTexTbl con with Not_found ->
                                                    failwith ("The LaTeX code of the connective " ^ con ^ " was not found. Please verify the specification file.") in 
			                               conTex ^ "\\Delta_{" ^ (Prints.remSpecial subLabel) ^ "}^{" ^ (string_of_int(generateIndex())) ^ "}, " ^ acc
		                                ) lst ""
    | _ -> failwith ("Error: the subexponential " ^ subLabel ^ " can not be printed.")
                    
  (* Prints formula variables, considering the right side and colorize the*)
  (* formula if it corresponds to the rule that will be applied. If a for-*)
  (* mula appears in a wrong context, a warning will be printed.          *)
  let toStringForms formulas side subLabel currentHeight mainRule = 
    (List.fold_right (fun f acc ->
                      let formSide = Specification.getSide f in
                      let sameSide = Subexponentials.isSameSide subLabel formSide in
                      match sameSide with
                      | true -> if formSide = side then begin
		                                let rule = Specification.getObjectLogicMainFormula f in
		                                if rule = mainRule then (colorizeForm f currentHeight) ^ ", " ^ acc
		                                else (Prints.termToTexString (Specification.getObjectLogicMainFormula f)) ^ ", " ^ acc end
		                            else acc
                      | false -> (print_string ("\nWarning: the following formula can't belong to the context "
		                                            ^ subLabel ^ ": " ^ (Prints.termToString f) ^ "\nPlease verify your especification.\n"); acc)
                     ) formulas "")
      
  let printFormList f = List.fold_right (fun f' acc -> (Prints.termToTexString (Specification.getHeadPredicate f')) ^ ", " ^ acc) f ""
                                        
  (* Subexponentials with index < 0 means that the context should not be *)
  (* written, just the formulas.                                         *)
  let toTexString ctx side maxIndex mainRule currentHeight = 
    (*List.fold_right (fun ((n, i), f) acc -> "\\Gamma_{" ^ (Prints.remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "} ; " ^ (printFormList f) ^ acc) ctx.lst ""*)
    let subLst = Subexponentials.getAllValid () in
    let slotToTex ctx side sub currentHeight =
    (* Prints context variables *)
    (List.fold_right (fun ((n, i), f) acc ->
      let correctSide = ((n = sub) && (Subexponentials.isSameSide n side)) in
      match (f, correctSide, i) with
      | (_, _, -1) -> acc
      | ([], true, _) -> (toStringVariable n i maxIndex side) ^ acc
      | (f', true, _) -> (toStringVariable n i maxIndex side) ^ (toStringForms f' side n currentHeight mainRule) ^ acc
      | _ -> acc
    ) ctx.lst "") ^
    (* Prints formula variables *)
    (List.fold_right (fun ((n, i), f) acc ->
      let correctSide = (((Prints.remSpecial n) = sub) && (Subexponentials.isSameSide (Prints.remSpecial n) side)) in
      match (side, correctSide, i) with
      | ("l", true, -1)  -> (toStringForms f "l" (Prints.remSpecial n) currentHeight mainRule) ^ acc
      | ("r", true, -1) -> (toStringForms f "r" (Prints.remSpecial n) currentHeight mainRule) ^ acc
      | _ -> acc
    ) ctx.lst "") in
    (* Prints all the slots *)
    let slotString = List.fold_right (fun sub acc ->
      match Subexponentials.isSameSide sub side with
        | false -> acc
        | true ->
          match remComma (slotToTex ctx side sub currentHeight) with
            | "" -> begin match acc with
              (*| "" -> " \\cdot " ^ acc*)
              | _ -> begin
                      let (arity, side) = Hashtbl.find Subexponentials.ctxTbl sub in
                      if (arity = SINGLE) && (side = RIGHT) then "; {}C " ^ acc
                      else "; {}\\cdot{} " ^ acc
                     end
            end
            | str -> begin match acc with
              (*| "" -> str ^ " " ^ acc*)
              | _ -> ";{} " ^ str ^ acc
            end
    ) subLst "" in
    try String.sub slotString 1 ((String.length slotString) - 1)
    with Invalid_argument(_) -> slotString
  
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
  
  let toTexString seq index mainRule currentHeight = 
    (OlContext.toTexString seq.ctx "l" index mainRule currentHeight) ^ " \\vdash " ^ (OlContext.toTexString seq.ctx "r" index mainRule currentHeight)

end;;

module type OLPROOFTREE =
  sig

    type prooftree = {
      mutable conclusion : OlSequent.sequent;
      mutable premisses : prooftree list;
      mutable rule : llrule option}
    
    val create : OlSequent.sequent -> llrule option -> prooftree
    val getConclusion : prooftree -> OlSequent.sequent
    val getContextFromPt : prooftree -> OlContext.context
    val toPermutation : prooftree -> unit
    val toTexString : prooftree -> string
    val toMacroRule : prooftree -> unit
    val isLeaf : prooftree -> bool
    val isOpenLeaf : prooftree -> bool
    val isClosedLeaf : prooftree -> bool
    val maxIndex : prooftree -> int
  
  end

module OlProofTree : OLPROOFTREE = struct
  
  type prooftree = {
    mutable conclusion : OlSequent.sequent;
    mutable premisses : prooftree list;
    mutable rule : llrule option
  }

  let currentHeight = ref (-1)              
  
  let create sq rl = {
    conclusion = sq;
    premisses = [];
    rule = rl;
  }

  let getConclusion pt = pt.conclusion
  
  let getContextFromPt pt = OlSequent.getContext (getConclusion pt)
  
  let getRule pt = pt.rule

  let isLeaf pt = (pt.premisses = [])

  let isOpen pt = (pt.rule = None)

  let isOpenLeaf pt = (isLeaf pt) && (isOpen pt)

  let isClosedLeaf pt = (isLeaf pt) && (not (isOpen pt))
  
  let counter () = if (!currentHeight + 1) > 1 then currentHeight := 0
                   else currentHeight := !currentHeight + 1; !currentHeight
  
  let getPol pt = 
    let conclusion = getConclusion pt in
    conclusion.OlSequent.pol

  let toPermutation olPt = 
    let firstPt = List.hd olPt.premisses in
    let rec getSeq' pt = 
      match (pt.premisses, getPol pt) with 
      | ([], ASYN) -> 
				begin
				  match pt.rule with 
				  | Some(r) -> []
				  | None -> [pt]
				end
      | (lpt, _) -> List.concat (List.map (fun p -> getSeq' p) lpt) in      
    let rec getSeq pt =
        match pt.premisses with
        | [] -> 
          begin
            match (getRule pt) with 
            | Some(r) -> []
            | None -> [pt]
          end
        | _ -> begin match (getPol pt) with
 	 		    | ASYN ->
 	 		      if (List.exists (fun el -> (getPol el) = SYNC) pt.premisses) then
 	 		        let nextPt = List.find (fun el -> (getPol el) = SYNC) pt.premisses in
              nextPt.premisses <- getSeq' nextPt;
 	 		        [nextPt]
 	 		      else List.concat (List.map (fun p -> getSeq p) pt.premisses)
 	 		    | SYNC -> 
 	 		      List.concat (List.map (fun p -> getSeq p) pt.premisses)
 	 		    end in
    let newPtList = getSeq firstPt in
    olPt.premisses <- newPtList;
    olPt.conclusion <- firstPt.conclusion
    
  let toMacroRule olPt =
    let firstPt = List.hd olPt.premisses in
    let rec getOpenLeaves pt = 
      match pt.rule with
      | Some(rule) -> List.concat (List.map (fun p -> getOpenLeaves p) pt.premisses)
      | None -> [pt] in
    let newPremisses = getOpenLeaves olPt in
    olPt.conclusion <- firstPt.conclusion;
    olPt.premisses <- newPremisses
    
  let maxIndex pt = 
    let index = ref (-1) in
    let rec getSeq pt = 
      match pt.rule with
      | Some(rule) -> if pt.premisses = [] then [pt] else List.concat (List.map (fun p -> getSeq p) pt.premisses)
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
	      let topproof = match pt.premisses with
	        | [] -> ""
	        | hd::tl -> (toTexString' hd (level + 1))^(List.fold_right (fun el acc -> "\n\\quad\n"^(toTexString' el (level + 1))) tl "") 
	      in
        let pred = List.hd seq.OlSequent.goals in
        let ruleNameTex = Specification.getRuleName pred in
	      (*"\\infer[" ^ ruleNameTex ^ "]{" ^ (OlSequent.toTexString (getConclusion pt)) ^ "}\n{" ^ topproof ^ "}"*)
	      "\\cfrac{" ^ topproof ^ "}\n{" ^ (OlSequent.toTexString (getConclusion pt) index mainRule level) ^ "} \\;\\; " ^ ruleNameTex 
      (* FIXME: using ZERO as a workaround... *)
      | None -> (OlSequent.toTexString (getConclusion pt) index ZERO level)
    in toTexString' pt 0

end;;

(* TODO: 
 * (1) refactor the methods so that they take only a bipole, and not a bipole list.
 * (2) do not transform the full tree into an olTree. With the new algorithm
 * this should no longer be necessary.
 *
 * Possible signature (initial idea):
 * private type context = string * int
 * private type rewritingRules = (context, (context list * terms list)) Hashtbl.t
 * private val computeRewritingRules : ProofTreeSchema.prooftree -> Constraints.constraintset -> rewritingRules
 * private val applyRewriting : ProofTreeSchema.prooftree ->  rewritingRules -> OlProofTree
 * val toObjectLogic : ProofTreeSchema.prooftree -> Constraints.constraintset -> OlProofTree.prooftree
 *)
module type REWRITING = 
  sig
  
    type derivation = ProofTreeSchema.prooftree * Constraints.constraintset
    type ol_derivation = OlProofTree.prooftree * Constraints.constraintset
    val reconstruct_tree : ProofTreeSchema.prooftree -> OlProofTree.prooftree
    val reconstruct_derivations : derivation list -> ol_derivation list
    val reconstruct_derivations_pair : (derivation * derivation) list -> (ol_derivation * ol_derivation) list
    val apply_model : OlProofTree.prooftree -> Constraints.constraintset -> unit
    val rewrite_derivations : ol_derivation list -> unit
    val rewrite_derivations_pair : (ol_derivation * ol_derivation) list -> unit

  end

module Rewriting : REWRITING = struct

  type sub = string * int
  type derivation = ProofTreeSchema.prooftree * Constraints.constraintset
  type ol_derivation = OlProofTree.prooftree * Constraints.constraintset
                                            
  (* ProofTreeSchema and OlProofTree are different, the former has sequents
   * sequents that have contexts of type ContextSchema, which consists of
   * a hashtable of (string * int) as key and terms list as content. The latter
   * has sequents that have contexts of type OlContext, which contains a list of 
   * ((string * int) * list of formulas)   
   *)
  let rec reconstruct_tree pt =
    let seq = ProofTreeSchema.getConclusion pt in
    let rule = ProofTreeSchema.getRule pt in
    let ctx = SequentSchema.getContext seq in
    let sub_lst = Hashtbl.fold (fun s i acc -> 
                                (s, i) :: acc
                               ) ctx.ContextSchema.hash [] in
    let context = OlContext.create sub_lst in
    let goals = SequentSchema.getGoals seq in
    let pol = SequentSchema.getPhase seq in
    let sequent = OlSequent.create context goals pol in
    let olPt = OlProofTree.create sequent rule in
    match pt.ProofTreeSchema.premises with
    | [] -> olPt
    | lst -> olPt.OlProofTree.premisses <- List.map reconstruct_tree lst;
             olPt
               
  let reconstruct_derivations drvt_lst = 
    List.map (fun (pt, model) -> (reconstruct_tree pt, model)) drvt_lst
    
  let reconstruct_derivations_pair drvt_pair_lst = 
    List.map (fun ((pt1, model1), (pt2, model2)) ->
              ((reconstruct_tree pt1, model1), (reconstruct_tree pt2, model2))
             ) drvt_pair_lst
  
  (* let print_subexp (str, i) = print_string (str ^ (string_of_int i)) *)

  (* let print_subexp_endline (str, i) = print_endline (str ^ (string_of_int i)) *)
  
  (* let print_hashtbl rewrite_ht = print_endline "------------ Beginnning -----------"; *)
  (*   Hashtbl.iter (fun k (sublst, flist) -> *)
  (*     print_subexp k; *)
  (*     print_string " -> "; *)
  (*     List.iter (fun sub -> print_subexp sub; print_string ", ") sublst; *)
  (*     List.iter (fun t -> print_string ((Prints.termToTexString t) ^ ", ")) flist; *)
  (*     print_string "\n" *)
  (*   ) rewrite_ht; *)
  (*   print_endline "------------ End -----------" *)

  (* Creates a list with n copies of f *)
  (* TODO: Move this functions to another file or module *)
  let rec flist f n =
    match n with
    | 0 -> []
    | n -> f :: (flist f (n-1))

  let rec remove_f f l =
    match l with
    | [] -> failwith ("[ERROR] Formula not found.")
    | h::t -> if f = h then t else h::(remove_f f t)
                    
  let filter_subexponentials lst =
    List.fold_right (fun (sub, f) acc ->
                     match (List.mem (fst(sub)) (Subexponentials.getAllValid ())) with
                     | true -> (sub, f) :: acc
                     | false -> acc
                    ) lst []

  let compute_rewrite_sequent seq model rewrite_ht max_index is_closed_leaf is_open_leaf =
    (* New context variables are created when we have IN(G, F, n) -> G*, F1, ..., Fn. G* doesn't occur on the proof tree
     * TODO: This solution using references is not the best one 
     *)
    let i = ref (max_index+1) in
    let count () = i := !i + 1; !i in
    (* Rewritten algorithm *)
    let ctx = OlSequent.getContext seq in
    ctx.OlContext.lst <- filter_subexponentials ctx.OlContext.lst;
    List.iter (fun (c, f) ->
               match is_open_leaf || is_closed_leaf with
               | true ->
                  List.iter (fun cstr ->
                             match cstr with
                             (* EMP(G) => G -> . *)
                             | EMP (c') ->
                                (if c' = c then
                                   (try match Hashtbl.find rewrite_ht c' with
                                        | ([], []) -> ()
                                        | _ -> failwith ("[ERROR] " ^ (OlContext.subToString c') ^ " should be empty.")
                                    with Not_found -> Hashtbl.replace rewrite_ht c' ([], []))
                                 else () )

                             (* IN(F, G, n) => G -> rwt(G), F (if rwt(G) is empty then rwt(G) = G *)
                             | IN (t, c', n) ->
                                (if c' = c then
                                   (try match Hashtbl.find rewrite_ht c' with
                                        | (sublst, flst) ->
                                           if not (List.exists (fun f -> t = f) flst) then
                                             Hashtbl.replace rewrite_ht c' (sublst, ((flist t n) @ flst))
                                           else ()
                                    with Not_found ->
                                      (match (is_closed_leaf, (Subexponentials.isUnbounded (fst(c')))) with
                                       | (true, false) -> Hashtbl.add rewrite_ht c' ([], (flist t n))
                                       | (_, _) -> let new_ctx = ((fst(c')), count()) in
                                                   Hashtbl.add rewrite_ht c' ([new_ctx], (flist t n))))
                                 else () )
                             | _ -> ()
                            ) model.lst
               | false ->
                  List.iter (fun cstr ->
                             match cstr with
                             (* EMP(G) =>
                              * 1. if rwt(G) is empty then G -> .
                              * 2. if rwt(G) is not empty then forall Gi in rwt(G)
                              *    forall k on the hashtable: k -> rwt(k) - Gi
                              *    and G -> .
                              *) 
                             | EMP (c') ->
                                (if c' = c then
                                   (try match Hashtbl.find rewrite_ht c' with
                                        | ([], []) -> ()
                                        | (sublst, flst) ->
                                           (List.iter (fun s ->
                                                       Hashtbl.iter (fun k (sublst', flst') ->
                                                                     Hashtbl.replace rewrite_ht k ((List.filter (fun s' -> s' <> s) sublst'), flst')
                                                                    ) rewrite_ht;
                                                      ) sublst;
                                            Hashtbl.replace rewrite_ht c' ([], []))
                                    with Not_found -> Hashtbl.replace rewrite_ht c' ([], []))
                                 else () )

                             (* UNION(G1, G2, G3) => G3 -> rwt(G1), rwt(G2) (if rwt(Gn) is empty then rwt(Gn) = Gn, where n = {1,2}) *)
                             | UNION (c1, c2, c') ->
                                (if c' = c then
                                   (let (sublst1, flst1) = try Hashtbl.find rewrite_ht c1 with Not_found -> ([c1], []) in
                                    let (sublst2, flst2) = try Hashtbl.find rewrite_ht c2 with Not_found -> ([c2], []) in
                                    Hashtbl.replace rewrite_ht c' (sublst1 @ sublst2, flst1 @ flst2))
                                 else () )

                             (* SETMINUS(G1, F, G0) => 
                              * 1. rwt(G0) is empty, so G0 -> rwt(G1) - F (if rwt(G1) is empty then the constraint will be processed on another sequent)
                              * 2. rwt(G0) is not empty, so rwt(G0) -> rwt(G1) (this is some kind of unification of context variables)
                              *    forall k on the hashtable: k -> rwt(G0) => k -> rwt(G1)
                              *)
                             | SETMINUS (c1, t, c') ->
                                (if c' = c then
                                   (try match Hashtbl.find rewrite_ht c1 with
                                        | (sublst, flst) ->
                                           (try match Hashtbl.find rewrite_ht c' with
                                                | (sublst', flst') ->
                                                   (if ((List.length sublst) > 0) && ((List.length sublst') > 0) &&
                                                         (not ((Hashtbl.mem rewrite_ht (List.hd sublst)) ||
                                                                 (Hashtbl.mem rewrite_ht (List.hd sublst')))) &&
                                                           sublst <> sublst' && flst' = (remove_f t flst) then
                                                      (if (List.hd sublst) > (List.hd sublst') then
                                                         Hashtbl.iter (fun k (s, f) ->
                                                                       let _s = List.map (fun s' ->
                                                                                          if s' = (List.hd sublst') then
                                                                                            (List.hd sublst)
                                                                                          else s') s in
                                                                       Hashtbl.replace rewrite_ht k (_s, f)
                                                                      ) rewrite_ht
                                                       else Hashtbl.iter (fun k (s, f) ->
                                                                          let _s = List.map (fun s' ->
                                                                                             if s' = (List.hd sublst) then
                                                                                               (List.hd sublst')
                                                                                             else s') s in
                                                                          Hashtbl.replace rewrite_ht k (_s, f)
                                                                         ) rewrite_ht)
                                                    else ())
                                            with Not_found -> Hashtbl.add rewrite_ht c' (sublst, remove_f t flst))
                                    with Not_found -> ())
                                 else () )
                             | _ -> ()
                            ) model.lst
              ) ctx.OlContext.lst
                                                 
  let rec compute_rewrite_rules olpt model rewrite_ht =
    let max_index = OlProofTree.maxIndex olpt in
    match (OlProofTree.isClosedLeaf olpt, OlProofTree.isOpenLeaf olpt) with
    | (false, true) ->
       compute_rewrite_sequent olpt.OlProofTree.conclusion model rewrite_ht max_index false true
    | (true, false) ->
       compute_rewrite_sequent olpt.OlProofTree.conclusion model rewrite_ht max_index true false
    | (false, false) ->
       List.iter (fun pt -> compute_rewrite_rules pt model rewrite_ht) olpt.OlProofTree.premisses;
       compute_rewrite_sequent olpt.OlProofTree.conclusion model rewrite_ht max_index false false

  let rewrite_sequent seq rewrite_ht =
    let ctx = OlSequent.getContext seq in
    let newCtx = List.fold_right (fun (c, f) acc ->
                               let (sublst, flst) = try Hashtbl.find rewrite_ht c
                                                    with Not_found -> ([c], f) in
                               (List.map (fun s -> (s, [])) sublst) @ [(((fst(c)), -1), flst)] @ acc
                              ) ctx.OlContext.lst [] in
    ctx.OlContext.lst <- newCtx; seq

  let rec rewrite_tree olpt rewrite_ht =
    let seq = OlProofTree.getConclusion olpt in
    match olpt.OlProofTree.premisses with
    | [] -> olpt.OlProofTree.conclusion <- (rewrite_sequent seq rewrite_ht)
    | lst -> List.iter (fun pt -> rewrite_tree pt rewrite_ht) lst;
             olpt.OlProofTree.conclusion <- (rewrite_sequent seq rewrite_ht)

  let apply_model olpt model =
    let rewrite_ht : (ctx, (ctx list) * (terms list)) Hashtbl.t = Hashtbl.create 100 in
    compute_rewrite_rules olpt model rewrite_ht;
    rewrite_tree olpt rewrite_ht;
    Hashtbl.reset rewrite_ht

  let rewrite_derivations ol_drvt =
    List.iter (fun (olpt, model) ->
      apply_model olpt model
    ) ol_drvt

  let rewrite_derivations_pair ol_drvt_pair =
    List.iter (fun ((olpt1, model1), (olpt2, model2)) ->
      apply_model olpt1 model1;
      apply_model olpt2 model2
    ) ol_drvt_pair

end;;

(* TODO: make it more modular? *)
(* Discuss it with Leo. [Giselle]*)
let apply_permute drvt_pair_lst = begin
  let olPt = ref [] in
  olPt := Rewriting.reconstruct_derivations_pair drvt_pair_lst;
  Rewriting.rewrite_derivations_pair !olPt;
  List.iter (fun ((olt1, model1), (olt2, model2)) -> 
    OlProofTree.toPermutation olt1;
    OlProofTree.toPermutation olt2;
  ) !olPt;
  !olPt
end ;;

let apply_perm_not_found perm_not_found = begin
  let olPt = ref [] in
  olPt := Rewriting.reconstruct_derivations perm_not_found;
  Rewriting.rewrite_derivations !olPt;
  !olPt
end ;;

let apply_derivation bipole = begin
  let (pt, model) = bipole in
  let olpt = Rewriting.reconstruct_tree pt in
  Rewriting.apply_model olpt model;
  OlProofTree.toMacroRule olpt;
  olpt
end ;;
