(**************************************)
(*                                    *)
(*    Checking if two rules are       *)
(*            permutable              *)
(*                                    *)
(*  Giselle Machado Reis              *)
(*  2013                              *)
(*                                    *)
(**************************************)

open Sequent
open Ol

(* Generates all possible derivations of spec1/spec2 (bottom-up) *)
let derive2 spec1 spec2 =

  (* Initial configuration *)
  let context = ContextSchema.createFresh () in
  let sequent = SequentSchema.createAsyn context [] in
  let in1 = Constraints.isIn spec1 "$gamma" context in
  let in2 = Constraints.isIn spec2 "$gamma" context in
  (* TODO: add the constraint that a context should have only one formula?? *)
  let constraints = Constraints.union in1 in2 in

  print_endline "====================== Initial constraints =====================";
  print_endline (Constraints.toString constraints);
  print_endline "================================================================";

  (* Compute possible bipoles for spec1 *)
  let bipoles1 = Bipole.deriveBipole sequent spec1 constraints in

  (* Try to derive spec2 in each open leaf of each bipole of spec1 *)
  List.fold_right (fun (pt1, mdl) bp ->
    (* This is a list of lists... each open leaf has a list of (proof tree *
       model) and these lists are the elements of the resulting list. *)
    let leafDerivations2over1 = List.fold_right (fun open_leaf acc ->
      match (Bipole.deriveBipole open_leaf spec2 mdl) with
        | [] -> acc
        | lst -> lst :: acc
    ) (ProofTreeSchema.getOpenLeaves pt1) []
    in

    (*let size = List.length leafDerivations2over1 in
    print_endline ("Leaf derivations: " ^ (string_of_int size));*)

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
    ) (Basic.cartesianProduct leafDerivations2over1) [] in
  
    bipoles2over1 @ bp

  ) bipoles1 []
;;

let permute spec1 spec2 = 
  let bipoles12 = derive2 spec1 spec2 in
  let bipoles21 = derive2 spec2 spec1 in
  
  (* GR: Prints all possible bipoles/models in a latex file. Make a separate
  function out of this.*)
  (*print_endline "\\documentclass[a4paper, 11pt]{article}\n\n\
  \\usepackage{amsmath}\n\
  \\usepackage{stmaryrd}\n\
  \\usepackage[margin=1cm]{geometry}\n\
  \\usepackage{proof}\n\n\
  \\begin{document}\n\n";

  print_endline ("\\section{Possible bipoles for $" ^ (Prints.termToTexString spec1) ^ "$ / $" ^ (Prints.termToTexString spec2) ^ "$:} \n");
  List.iter (fun (pt, model) ->
    print_endline "{\\small";
    print_endline "\\[";
    print_endline (ProofTreeSchema.toTexString pt);
    print_endline "\\]";
    print_endline "}";
    print_endline "CONSTRAINTS\n";
    print_endline (Constraints.toTexString model);
  ) bipoles12;

  print_endline ("\\section{Possible bipoles for $" ^ (Prints.termToTexString spec2) ^ "$ / $" ^ (Prints.termToTexString spec1) ^ "$:} \n");
  List.iter (fun (pt, model) ->
    print_endline "{\\small";
    print_endline "\\[";
    print_endline (ProofTreeSchema.toTexString pt);
    print_endline "\\]";
    print_endline "}";
    print_endline "CONSTRAINTS\n";
    print_endline (Constraints.toTexString model);
  ) bipoles21;
  

  print_endline "\\end{document}";*)


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

(* Prints the permutations of rules to a latex file *)
let printPermutations fileName perm_bipoles = 
  let file = open_out ("proofsTex/"^fileName^".tex") in
  let olPt = apply_permute perm_bipoles in
  Printf.fprintf file "%s" Prints.texFileHeader;
  List.iter (fun (b12, b21) ->
 	  Printf.fprintf file "%s" "{\\scriptsize";
 	  Printf.fprintf file "%s" "\\[";
 	  Printf.fprintf file "%s" (OlProofTree.toTexString (fst(b12)));
 	  Printf.fprintf file "\n\\quad\\rightsquigarrow\\quad\n";
 	  Printf.fprintf file "%s" (OlProofTree.toTexString (fst(b21)));
 	  Printf.fprintf file "%s" "\\]";
 	  Printf.fprintf file "%s" "}";
 	  Printf.fprintf file "%s" "\\\[0.7cm]";
  ) olPt;
  Printf.fprintf file "%s" Prints.texFileFooter;
  close_out file
;;
