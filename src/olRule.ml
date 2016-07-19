(****************************************************)
(*                                                  *)
(*  Leonardo Lima, 2013                             *)
(*                                                  *)
(*  Implements the Object Logic (OL), solving the   *)
(*  constraints and making each sequent readable.   *)
(*                                                  *)
(****************************************************)

open Constraints 
open ContextSchema
open Llrules
open ProofTreeSchema 
open Sequent
open Types
open Subexponentials

module type OLCONTEXT =
  sig
  
    type ctxVar = string * int
    type ctx = ctxVar * terms list
    type context = { mutable lst : ctx list  }
    val create : ctxVar list -> context
    val toStringForms : terms list -> string -> string -> int -> terms -> string
    val toTexString : context -> string -> int -> terms -> int -> string
    val subToString : ctxVar -> string
  
  end

module OlContext : OLCONTEXT = struct

  type ctxVar = string * int
  
  type ctx = ctxVar * terms list
  
  type context = {
    mutable lst : ctx list;
  }
  
  let create ctxList = {
    lst = List.map (fun ctx -> (ctx, [])) ctxList;
  }

  let remComma str = (try String.sub str 0 ((String.length str) - 2) with Invalid_argument(_) -> str)

  let subToString (s, i) = s ^ "_" ^ string_of_int(i)
  
  (* Colorize a formula according to its height on the prooftree *)
  let colorizeForm f currentHeight =
    match (currentHeight mod 2) with
    | 0 -> "{\\color{red}" ^ (Prints.termToTexString (Specification.getObjectLogicMainFormula f)) ^ "}"
    | 1 -> "{\\color{blue}" ^ (Prints.termToTexString (Specification.getObjectLogicMainFormula f)) ^ "}"
    | _ -> failwith "Wrong result of module operation (colorizeForm)."
    
  (* Print context variables according to their side; it also takes into account 
   * if the subexponential has connectives declared on the specification
   * TODO: Analyze the cases below where there is a list of connectives
   * Doesn't the arity matter?
   *)
  let toStringVariable subLabel index maxIndex side nofm = 
    let k = ref maxIndex in
    let generateIndex = (fun () -> k := !k+1; !k) in
    let conList = try Hashtbl.find Subexponentials.conTbl subLabel with Not_found -> [] in
    match (conList, side) with
    | ([], "l") -> "\\Gamma_{" ^ subLabel ^ "}^{" ^ (string_of_int index) ^ "}, "
    | ([], "r") -> let (arity, side) = Hashtbl.find Subexponentials.ctxTbl subLabel in
                   (match (arity, nofm) with
                    | (MANY, _) -> "\\Delta_{" ^ subLabel ^ "}^{" ^ (string_of_int index) ^ "}, "
                    | (SINGLE, true) -> "C"
                    | (SINGLE, false) -> "")
    | (lst, "l") -> List.fold_right (fun con acc -> 
			             let conTex = try Hashtbl.find Subexponentials.conTexTbl con 
						  with Not_found ->
						    failwith ("The LaTeX code of the connective " ^ con ^ 
								" was not found. Please verify the specification file.") in 
			             conTex ^ "\\Gamma_{" ^ subLabel ^ "}^{" ^ (string_of_int(generateIndex())) ^ "}, " ^ acc
		                    ) lst ""
    | (lst, "r") -> List.fold_right (fun con acc -> 
			             let conTex = try Hashtbl.find Subexponentials.conTexTbl con 
						  with Not_found ->
                                                    failwith ("The LaTeX code of the connective " ^ con ^ 
								" was not found. Please verify the specification file.") in 
			             conTex ^ "\\Delta_{" ^ subLabel ^ "}^{" ^ (string_of_int(generateIndex())) ^ "}, " ^ acc
		                    ) lst ""
    | _ -> failwith ("Error: the subexponential " ^ subLabel ^ " can not be printed.")
                    
  (* Print formula variables according to their side and colorize the
   * formula if it corresponds to the rule that will be applied
   *)
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
                      | false -> (print_string ("\nWarning: the following formula can't belong to the context " ^ subLabel ^ 
						  ": " ^ (Prints.termToString f) ^ "\nPlease verify your especification.\n"); acc)
                     ) formulas "")

  (* Context variables with index -1 should not be printed, just its formulas;
   * TODO: Change the data structure of contexts; Formulas don't have to be associated
   * with context variables, but with subexponential labels
   *)
  let toTexString ctx side maxIndex mainRule currentHeight = 
    let subLst = Subexponentials.getAllValid () in
    let slotToTex ctx side sub currentHeight =
      let s2 = (List.fold_right (fun ((n, i), f) acc ->
                                 let correctSide = (n = sub) && (Subexponentials.isSameSide n side) in
                                 match (side, correctSide, i) with
                                 | ("l", true, -1)  -> (toStringForms f "l" n currentHeight mainRule) ^ acc
                                 | ("r", true, -1) -> (toStringForms f "r" n currentHeight mainRule) ^ acc
                                 | _ -> acc
                                ) ctx.lst "") in
      let nofm = (s2 = "") in
      let s1 = (List.fold_right (fun ((n, i), f) acc ->
                                 let correctSide = ((n = sub) && (Subexponentials.isSameSide n side)) in
                                 match (f, correctSide, i) with
                                 | (_, _, -1) -> acc
                                 | ([], true, _) -> (let str = (toStringVariable n i maxIndex side nofm) in
                                                     match side with
                                                     | "r" -> (if str = "C" && acc = "C" then acc 
                                                               else str ^ acc)
                                                     | "l" -> str ^ acc)
                                 | (f', true, _) -> (toStringVariable n i maxIndex side nofm) ^ 
						    (toStringForms f' side n currentHeight mainRule) ^ acc
                                 | _ -> acc
                                ) ctx.lst "") in (s1 ^ s2) in
    let slotString = List.fold_right (fun sub acc ->
                                      match Subexponentials.isSameSide sub side with
                                      | false -> acc
                                      | true -> let _string = remComma (slotToTex ctx side sub currentHeight) in
                                                (match _string with
                                                 | "" -> "; {}\\cdot{} " ^ acc
                                                 | str ->  ";{} " ^ str ^ acc)
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
      mutable premises : prooftree list;
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

  let isLeaf pt = (pt.premises = [])

  let isOpen pt = (pt.rule = None)

  let isOpenLeaf pt = (isLeaf pt) && (isOpen pt)

  let isClosedLeaf pt = (isLeaf pt) && (not (isOpen pt))
  
  let getPol pt = 
    let conclusion = getConclusion pt in
    conclusion.OlSequent.pol

  let toPermutation olPt = 
    let firstPt = List.hd olPt.premises in
    let rec getSeq' pt = 
      match (pt.premises, getPol pt) with 
      | ([], ASYN) -> 
	 begin
	   match pt.rule with 
	   | Some(r) -> []
	   | None -> [pt]
	 end
      | (lpt, _) -> List.concat (List.map (fun p -> getSeq' p) lpt) in      
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
 	     end in
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
    let max = ref 0 in
    let rec getLeaves pt = 
      match pt.rule with
      | Some(rule) -> if pt.premises = [] then [pt] else List.concat (List.map (fun p -> getLeaves p) pt.premises)
      | None -> [pt] in
    let leaves = getLeaves pt in
    List.iter (fun olPt ->
	       let olSeq = getConclusion olPt in
	       let olCtx = OlSequent.getContext olSeq in
	       List.iter (fun ((s, i), l) -> if i > !max then max := i else ()) olCtx.OlContext.lst;
	      ) leaves; !max

  (* TODO: Rewrite this code avoiding references
   * The type of this function should be: OlProofTree -> OlProofTree
   *)
  let normalizeIndexes pt =
    let ctx_conc = getContextFromPt pt in
    let norm_ht : (OlContext.ctxVar, OlContext.ctxVar) Hashtbl.t = Hashtbl.create 100 in
    List.iter (fun ((s, i), f) ->
               if i >= 0 then
                 (let last_i = ref 0 in
                  Hashtbl.iter (fun (_s, _i) (_s', _i') ->
                                if s = _s && _i' > !last_i then last_i := _i'
                                else ()
                               ) norm_ht;
                  if !last_i <> 0 then
                    Hashtbl.add norm_ht (s, i) (s, (!last_i + 1))
                  else
                    Hashtbl.add norm_ht (s, i) (s, 1))
              ) ctx_conc.OlContext.lst;
    let normalizeCtx lst =
      List.fold_right (fun ((s, i), f) acc ->
                       let sub_norm = try Hashtbl.find norm_ht (s, i)
                                      with Not_found -> (s, i) in
                       (sub_norm, f) :: acc
                      ) lst [] in
    let rec normalizeTree pt' =
      match pt'.rule with
      | None ->
         let ctx = getContextFromPt pt' in
         ctx.OlContext.lst <- normalizeCtx ctx.OlContext.lst
      | Some(r) ->
         let ctx = getContextFromPt pt' in
         ctx.OlContext.lst <- normalizeCtx ctx.OlContext.lst;
         List.iter (fun p -> normalizeTree p) pt'.premises in normalizeTree pt
    
  let toTexString pt =
    normalizeIndexes pt;
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
    val rebuild_tree : ProofTreeSchema.prooftree -> OlProofTree.prooftree
    val rebuild_derivations : derivation list -> ol_derivation list
    val rebuild_derivations_pair : (derivation * derivation) list -> (ol_derivation * ol_derivation) list
    val apply_model : OlProofTree.prooftree -> Constraints.constraintset -> unit
    val rewrite_derivations : ol_derivation list -> unit
    val rewrite_derivations_pair : (ol_derivation * ol_derivation) list -> unit

  end

module Rewriting : REWRITING = struct

  type derivation = ProofTreeSchema.prooftree * Constraints.constraintset
  type ol_derivation = OlProofTree.prooftree * Constraints.constraintset
                                            
  (* ProofTreeSchema and OlProofTree are different, the former has sequents
   * sequents that have contexts of type ContextSchema, which consists of
   * a hashtable of (string * int) as key and terms list as content. The latter
   * has sequents that have contexts of type OlContext, which contains a list of 
   * ((string * int) * list of formulas)   
   *)
  let rec rebuild_tree pt =
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
    let olpt = OlProofTree.create sequent rule in
    match pt.ProofTreeSchema.premises with
    | [] -> olpt
    | lst -> olpt.OlProofTree.premises <- List.map rebuild_tree lst;
             olpt
               
  let rebuild_derivations drvt_lst = 
    List.map (fun (pt, model) -> (rebuild_tree pt, model)) drvt_lst
    
  let rebuild_derivations_pair drvt_pair_lst = 
    List.map (fun ((pt1, model1), (pt2, model2)) ->
              ((rebuild_tree pt1, model1), (rebuild_tree pt2, model2))
             ) drvt_pair_lst
  
  let print_subexp (str, i) = print_string (str ^ (string_of_int i))

  let print_subexp_endline (str, i) = print_endline (str ^ (string_of_int i))
  
  let print_hashtbl rewrite_ht = 
    print_endline "----------- Beginnning -----";
    Hashtbl.iter (fun k (sublst, flist) ->
		  print_subexp k;
		  print_string " -> ";
		  List.iter (fun sub -> print_subexp sub; print_string ", ") sublst;
		  List.iter (fun t -> print_string ((Prints.termToTexString t) ^ ", ")) flist;
		  print_string "\n"
		 ) rewrite_ht;
    print_endline "----------- End ------------"

  (* Creates a list with n copies of f *)
  (* TODO: Move this functions to another file or module *)
  let rec flist f n =
    match n with
    | 0 -> []
    | n -> f :: (flist f (n-1))

  let rec remove_f f l =
    match l with
    | [] -> failwith ("[ERROR] Formula not found while processing MINUS. Please, take a look at the constraintset.")
    | h::t -> if f = h then t else h::(remove_f f t)

  let filter_constraints s lst =
    List.filter (fun cstr ->
                 match cstr with
                 | EMP (c) -> c = s
                 | IN (t, c, n) ->  c = s
                 | SETMINUS (c1, t, c) -> c = s 
                 | UNION (c1, c2, c) -> c = s
                ) lst

  let rec rearrange l =
    if (List.length (List.concat l)) = 0 then []
    else List.map List.hd l :: rearrange (List.map List.tl l)

  let i = ref 0
  let set_max_index max_index = i := max_index + 1
  let count () = i := !i + 1; !i

  let unify_variables sublst sublst' rewrite_ht =
    let unify_ht : (OlContext.ctxVar, OlContext.ctxVar list) Hashtbl.t = Hashtbl.create 100 in
    let new_variables1 = List.map (fun (s, i) ->
				   List.map (fun (s', i') -> 
					     (s', count())
					    ) sublst'
				  ) sublst in
    let new_variables2 = rearrange new_variables1 in
    List.iter2 (fun s lst -> Hashtbl.add unify_ht s lst) sublst new_variables1;
    List.iter2 (fun s lst -> Hashtbl.add unify_ht s lst) sublst' new_variables2;
    List.iter (fun s ->
	       Hashtbl.iter (fun k (slst, flst) ->
			     let new_slst = List.fold_right (fun s' acc ->
							     if s = s' then
							       let new_rwt = Hashtbl.find unify_ht s in
							       Hashtbl.add rewrite_ht s (new_rwt, []);
							       new_rwt @ acc
							     else s' :: acc
							    ) slst [] in
			     Hashtbl.replace rewrite_ht k (new_slst, flst)
			    ) rewrite_ht
	      ) sublst;
    List.iter (fun s ->
	       Hashtbl.iter (fun k (slst, flst) ->
			     let new_slst = List.fold_right (fun s' acc ->
							     if s = s' then
							       let new_rwt = Hashtbl.find unify_ht s in
							       Hashtbl.add rewrite_ht s (new_rwt, []);
							       new_rwt @ acc
							     else s' :: acc
							    ) slst [] in
			     Hashtbl.replace rewrite_ht k (new_slst, flst)
			    ) rewrite_ht
	      ) sublst'

  let compute_rewrite_sequent seq model rewrite_ht is_closed_leaf is_open_leaf =
    (* New context variables are created when we have IN(G, F, n) -> G*, F1, ..., Fn. G* doesn't occur on the proof tree
     * TODO: This solution using references is not the best one 
     *)
    let ctx = OlSequent.getContext seq in
    ctx.OlContext.lst <- Subexponentials.filter_subexponentials ctx.OlContext.lst;
    List.iter (fun (c, f) ->
               match is_open_leaf || is_closed_leaf with
               | true ->
                  List.iter (fun cstr ->
                             match cstr with
                             (* EMP(G) => G -> . *)
                             | EMP (c') ->
                                (try match Hashtbl.find rewrite_ht c' with
                                     | ([], []) -> ()
                                     | _ -> failwith ("[ERROR] " ^ (OlContext.subToString c') ^ " should be empty.")
                                 with Not_found -> Hashtbl.replace rewrite_ht c' ([], []))

                             (* IN(F, G, n) => G -> rwt(G), F (if rwt(G) is empty then rwt(G) = G *)
                             | IN (t, c', n) ->
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
                             | _ -> ()
                            ) (filter_constraints c model.lst)
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
                                (try match Hashtbl.find rewrite_ht c' with
                                     | ([], []) -> ()
                                     | (sublst, flst) ->
                                        (List.iter (fun s ->
                                                    Hashtbl.iter (fun k (sublst', flst') ->
                                                                  Hashtbl.replace rewrite_ht k ((List.filter (fun s' -> 
													      s' <> s
													     ) sublst'), flst')
                                                                 ) rewrite_ht;
                                                   ) sublst;
                                         Hashtbl.replace rewrite_ht c' ([], []))
                                 with Not_found -> Hashtbl.replace rewrite_ht c' ([], []))

                             (* UNION(G1, G2, G3) => G3 -> rwt(G1), rwt(G2) (if rwt(Gn) is empty then rwt(Gn) = Gn, where n = {1,2}) *)
                             | UNION (c1, c2, c') ->
                                (try match Hashtbl.find rewrite_ht c' with
                                     | (sublst, flst) -> ()
                                 with Not_found ->
                                (let (sublst1, flst1) = try Hashtbl.find rewrite_ht c1 with Not_found -> ([c1], []) in
                                 let (sublst2, flst2) = try Hashtbl.find rewrite_ht c2 with Not_found -> ([c2], []) in
                                 Hashtbl.add rewrite_ht c' (sublst1 @ sublst2, flst1 @ flst2)))

                             (* SETMINUS(G1, F, G0) => 
                              * 1. rwt(G0) is empty, so G0 -> rwt(G1) - F (if rwt(G1) is empty then the constraint will be processed on another sequent)
                              * 2. rwt(G0) is not empty, so rwt(G0) -> rwt(G1) (this is some kind of unification of context variables)
                              *    forall k on the hashtable: k -> rwt(G0) => k -> rwt(G1)
                              *)
                             | SETMINUS (c1, t, c') ->
                                (try match Hashtbl.find rewrite_ht c1 with
                                     | (sublst, flst) ->
                                        (try match Hashtbl.find rewrite_ht c' with
                                             | (sublst', flst') ->
						(if (List.sort compare sublst) <> (List.sort compare sublst') && 
						     flst' = (remove_f t flst) then unify_variables sublst sublst' rewrite_ht
						 else ())
					 (* If rwt(c1) and rwt(c') are empty, then just process the constraint as usual *)
                                         with Not_found -> Hashtbl.add rewrite_ht c' (sublst, remove_f t flst))
				 (* If rwt(c1) is empty, then waits to process the constraint on another branch *)
                                 with Not_found -> ())
                             | _ -> ()
                            ) (filter_constraints c model.lst)
              ) ctx.OlContext.lst

  let rec compute_rewrite_rules olpt model rewrite_ht =
    match (OlProofTree.isClosedLeaf olpt, OlProofTree.isOpenLeaf olpt) with
    | (false, true) ->
       compute_rewrite_sequent olpt.OlProofTree.conclusion model rewrite_ht false true
    | (true, false) ->
       compute_rewrite_sequent olpt.OlProofTree.conclusion model rewrite_ht true false
    | (false, false) ->
       List.iter (fun pt -> compute_rewrite_rules pt model rewrite_ht) olpt.OlProofTree.premises;
       compute_rewrite_sequent olpt.OlProofTree.conclusion model rewrite_ht false false

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
    match olpt.OlProofTree.premises with
    | [] -> olpt.OlProofTree.conclusion <- (rewrite_sequent seq rewrite_ht)
    | lst -> List.iter (fun pt -> rewrite_tree pt rewrite_ht) lst;
             olpt.OlProofTree.conclusion <- (rewrite_sequent seq rewrite_ht)

  let apply_model olpt model =
    let rewrite_ht : (OlContext.ctxVar, (OlContext.ctxVar list) * (terms list)) Hashtbl.t = Hashtbl.create 100 in
    let max_index = OlProofTree.maxIndex olpt in
    set_max_index max_index;
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
  olPt := Rewriting.rebuild_derivations_pair drvt_pair_lst;
  Rewriting.rewrite_derivations_pair !olPt;
  List.iter (fun ((olt1, model1), (olt2, model2)) -> 
    OlProofTree.toPermutation olt1;
    OlProofTree.toPermutation olt2;
  ) !olPt;
  !olPt
end ;;

let apply_perm_not_found perm_not_found = begin
  let olPt = ref [] in
  olPt := Rewriting.rebuild_derivations perm_not_found;
  Rewriting.rewrite_derivations !olPt;
  !olPt
end ;;

let apply_derivation bipole = begin
  let (pt, model) = bipole in
  let olpt = Rewriting.rebuild_tree pt in
  Rewriting.apply_model olpt model;
  OlProofTree.toMacroRule olpt;
  olpt
end ;;
