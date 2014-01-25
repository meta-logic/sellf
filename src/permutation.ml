(**************************************)
(*                                    *)
(*    Checking if two rules are       *)
(*            permutable              *)
(*                                    *)
(*  Giselle Machado Reis              *)
(*  2013                              *)
(*                                    *)
(**************************************)

open Types
open Basic
open Bipole
open ContextSchema
open Dlv
open Ol
open ProofTreeSchema
open Sequent

module type PERMUTATION = 
  sig
    val derive2 : terms -> terms -> (ProofTreeSchema.prooftree * Constraints.constraintset) list
    val permute : terms -> terms -> ((ProofTreeSchema.prooftree * Constraints.constraintset) * (ProofTreeSchema.prooftree * Constraints.constraintset)) list * (ProofTreeSchema.prooftree * Constraints.constraintset) list
    val permutationsToTexString : (Ol.Derivation.bipole * Ol.Derivation.bipole) list -> string
    val nonPermutationsToTexString : Ol.Derivation.bipole list -> string
  end

module Permutation : PERMUTATION = struct

  (* Generates all possible derivations of spec1/spec2 (bottom-up) *)
  let derive2 spec1 spec2 =

    (* Initial configuration *)
    let context = ContextSchema.createFresh () in
    let sequent = SequentSchema.createAsyn context [] in

    (* Computing possible initial contexts for F1 (ignoring gamma and infty) *)
    let in1 = Constraints.inEndSequent spec1 context in

    (* Computing possible initial contexts for F2 (ignoring gamma and infty) *)
    let in2 = Constraints.inEndSequent spec2 context in

    (* We assume that there are two occurrences of these formulas. The initial
    models generated contain two 'in' clauses, one for each formula. *)
    let constraints = Constraints.times in1 in2 in

    (* Compute possible bipoles for spec1 *)
    let bipoles1 = Bipole.deriveBipole sequent spec1 constraints in

    (* Try to derive spec2 in each open leaf of each bipole of spec1 *)
    List.fold_right (fun (pt1, mdl) bp ->
      (* This is a list of lists... each open leaf has a list of (proof tree *
	model) and these lists are the elements of the resulting list. I.e.:
	open_leaf_1 : [(proof tree * model)]   
	open_leaf_2 : [(proof tree * model)]
	...
	open_leaf_n : [(proof tree * model)]   
      *)
      let leafDerivations2over1 = List.fold_right (fun open_leaf acc ->
	match (Bipole.deriveBipole open_leaf spec2 [mdl]) with
	  | [] -> acc
	  | lst -> lst :: acc
      ) (ProofTreeSchema.getOpenLeaves pt1) []
      in

      (* Combining the derivations

	Let ol1, ol2, ..., oln be the open leaves of derivation. Each open leaf
	contains a set of pairs (proof tree * model) which are the possible
	derivations for it. I.e.:

	l1 : [d1,1, ..., d1,k1]
	l2 : [d2,1, ..., d2,k2]
	...
	ln : [dn,1, ..., dn,kn]

	In order to obtain all possible derivations of both rules we need to find
	all sets S such that 1 <= |S| <= n and S contains *at most* one element
	from each open leaf. Note that the cross product of l1, ..., ln will give
	all such sets of size n, but not smaller. In order to obtain sets with
	less elements, we add a dummy element in each list which represents that
	no element from that list was chosen. Then, the cross product gives us
	exactly what we want once we remove the dummy elements from the sets.    
      *)

      (* Creating a list of options, in which NONE is the dummy element *)
      let leafDerivations_opt = List.map (fun lst -> 
	None :: (List.map (fun p -> Some(p)) lst)
      ) leafDerivations2over1 in

      (* Computing the cross product and removing the dummy elements *)
      let allLeafDerivations = List.map ( fun lst ->
	List.fold_right (fun p acc -> match p with
	  | Some(p) -> p :: acc
	  | None -> acc
	) lst []
      ) (Basic.cartesianProduct leafDerivations_opt) in


      let bipoles2over1 = List.fold_right (fun leaves bipoles ->
	let unionModels = List.fold_right (fun (proof, m) acc -> 
	  Constraints.union m acc
	) leaves (Constraints.create []) in
	let models = Dlv.getModels unionModels in
	List.fold_right (fun model accBp ->
	  match Constraints.isEmpty model with
	  | true -> bipoles
	  | false ->
	    let pt1copy = ProofTreeSchema.copy pt1 in
	    let bipole = List.fold_right (fun (leaf, _) pt ->
	      ProofTreeSchema.appendLeaf pt leaf
	    ) leaves pt1copy in
	    (bipole, model) :: accBp
	) models bipoles
      ) allLeafDerivations [] in
    
      bipoles2over1 @ bp

    ) bipoles1 []
  ;;

  (* The return value of this function is a pair: 
    ( [(a_1, a_2), ..., (a_{n-1}, a_n)], [b_1, ..., b_k] )

    in which the first element is a list of pairs of permutations found, and the
    secont element are the configurations of the rule for which no permutations
    were found.
  *)
  let permute spec1 spec2 =

    (* TODO: normalize the specifications. Do this in a more elegant way!! *)
    let rec instantiate_ex spec constLst = match spec with
      | EXISTS(s, i, f) ->
        let constant = CONST (List.hd constLst) in
      	let newf = Norm.hnorm (APP (ABS (s, 1, f), [constant])) in
      	instantiate_ex newf (List.tl constLst)
      | _ -> (spec, constLst)
    in
    (* We shouldn't have more than 4 existentially quantified variables... *)
    let constLst = ["b"; "a"; "d"; "c"; "e"] in
    let (spec1norm, rest) = instantiate_ex spec1 constLst in
    let (spec2norm, rest2) = instantiate_ex spec2 rest in

    let bipoles12 = derive2 spec1norm spec2norm in
    let bipoles21 = derive2 spec2norm spec1norm in

  (*
    For every bipole12 there exists a bipole21 such that for all open leaves of
    bipole21, this leaf can be proven given that a leaf of bipole12 is provable.
  *)

    List.fold_right (fun b12 acc ->
      try match List.find (fun b21 -> Dlv.proofImplies b12 b21) bipoles21 with
	| b -> ( (b12, b) :: fst(acc), snd(acc) )
      with Not_found -> ( fst(acc), b12 :: snd(acc) )
    ) bipoles12 ([], [])

  ;;

  let permutationsToTexString lst = 
    let olPt = apply_permute lst in
    List.fold_right (fun (b12, b21) acc ->
      "{\\scriptsize\n" ^ 
      "\\[\n" ^
      OlProofTree.toTexString (fst(b12)) ^
      "\n\\quad\\rightsquigarrow\\quad\n" ^
      OlProofTree.toTexString (fst(b21)) ^
      "\n\\]" ^
      "\n}" ^
      "\n\\\\[0.7cm]\n\n" ^ acc
    ) olPt ""
  ;;

  let nonPermutationsToTexString lst = 
    let olPt = apply_perm_not_found lst in
    List.fold_right (fun (olt, mdl) acc ->
      OlProofTree.toPermutationFormat olt;
      "{\\scriptsize\n" ^ 
      "\\[\n" ^
      OlProofTree.toTexString olt ^
      "\n\\]" ^
      "\n}" ^
      "\n\\\\[0.7cm]\n\n" ^ acc
    ) olPt ""

end;;


