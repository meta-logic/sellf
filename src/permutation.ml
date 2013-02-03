(* Code to check if two rules are permutable 
 *
 * Giselle Machado Reis 2011
 *
 *)

open Term
open Macro
open Structs
open ProofTree
open Constraints
open Lib
open Prints

(*
ctx(Ctx, Sub, Lin/Unb, Leaf, Tree) -> Denotes that the context Ctx belongs to the 
                                 linear/unbounded subexponential of the open leaf Leaf of the 
                                 tree Tree. *)

let rec genCtxFacts lvsLst treeNum lfNum = match lvsLst with
  | [] -> ""
  | lf :: tl ->
    let ctxs = getContexts (ProofTree.getConclusion lf) in
    Hashtbl.fold (fun name index acc -> 
      let treeName = ("tree"^(string_of_int treeNum) ) in
      let leafName = ("leaf"^(string_of_int lfNum) ) in
      let ctxName = ctxToStr (name, index) in
      let subexpType = subexpTypeToStr (type_of name) in
      let fact = "ctx("^ctxName^", "^(remSpecial name)^", "^subexpType^", "^leafName^", "^treeName^").\n" in
      (fact^acc)
    ) ctxs (genCtxFacts tl treeNum (lfNum+1))

let rec okStrAux sn en = match sn with
  | x when x = en -> "provIf(leaf"^(string_of_int x)^", _)."
  | y -> "provIf(leaf"^(string_of_int y)^", _), "^(okStrAux (sn+1) en)

let rec genOkStr startnum endnum = "ok :- "^(okStrAux startnum endnum)^"\n:- not ok.\n"

let counter = ref 0 

let permute r1 r2 = 
  (* Creating macro-rules for r1 *)
  initMacro r1; 
  rmacro (fun () ->
    if !verbose then begin
      print_endline "MACRO RULE FOR r1 *alone*";
      ProofTree.printLeaves !macrorule;
      Constraints.printConstraints !constrs;
      flush stdout;
    end;
    save_macro ();
  );
  let macrosr1 = !macrolst in
  (*print_string ("Number of macros for r1: "^(string_of_int (List.length macrosr1))^"\n");*)
  macrolst := [];

  (* Creating macro-rules for r2 *)
  Constraints.clear !constrs;
  (* Add one to start with fresh generic contexts *)
  let newCtx = ref (Hashtbl.create 100) in
  Hashtbl.iter (fun name index -> Hashtbl.add !newCtx name (index+1)) !macroctx;
  macroctx := Hashtbl.copy !newCtx;
  let ptr2 = ProofTree.create (SEQM(!newCtx, [], SYNC)) in
  initMacroFrom ptr2 ptr2 (Constraints.create ()) r2;
  rmacro (fun () ->
    if !verbose then begin
      print_endline "MACRO RULE FOR r2 *alone*";
      ProofTree.printLeaves !macrorule;
      Constraints.printConstraints !constrs;
      flush stdout;
    end;
    save_macro ();
  );
  let macrosr2 = !macrolst in
  (*print_string ("Number of macros for r2: "^(string_of_int (List.length macrosr2))^"\n");*)
  macrolst := [];

  let findPermutation0 (pt, clst) = 
    let ptCp = ProofTree.copy pt in
    let clstCp = Constraints.copy clst in
    let openlvsr1 = ProofTree.getOpenLeaves ptCp in
    let subsets1 = allnonemptysubsets openlvsr1 in
    if (List.length openlvsr1) = 0 then failwith "Macro rule of r1 has no open
      leaves to apply r2. Nothing can permute over an axiom because there is
      never something on top of an axiom =)";
    (* TODO: This permutation will occur iff r2/r1 has no open leaves. *)

    let findPermutation1 set1 = 
      
      (* Apply r2 over a set of leaves of macro-r1 *)
      (*print_endline ("Applying r1 over "^(string_of_int (List.length set))^" leaves of r2.");*)

      (* G: Important note
        I have decided to apply r2 over more than one premise of r1 because of
        the with/par permutation case of LL. In this case, I need to apply par
        in both premises of with. Also, from this moment on I started to ignore
        the head of the specification because it was generating models that were
        not satisfiable, namely, models that applied par on different occurences
        of the formuls on the right and left branches (e.g. (par a b) was in
        gamma on the left branch and in slin on the right branch). Now we can
        interpret that our system already applies definitions instead of
        deriving the whole formula. Which actually makes more sense since (par a
        b) should actually be in gamma (\infty).
      *)
     
      (* Continuation function for recursive call of rmacros *)
      let rec cont1 n () = 
        if n = 0 then begin
          if !verbose then begin
            print_endline "MACRO RULE FOR r2/r1";
            ProofTree.printLeaves !macrorule;
            Constraints.printConstraints !constrs;
            flush stdout
          end;
          save_macro ()
        end
        else begin
          let idx = (List.length set1)-n in
          initMacroFrom !macrorule (List.nth set1 idx) !constrs r2;
          rmacro (cont1 (n-1))
        end
      in
      ProofTree.mask pt ptCp;
      macrorule := ptCp;
      constrs := clstCp;
      initMacroFrom !macrorule (List.hd set1) !constrs r2;
      rmacro ( cont1 ((List.length set1)-1) );
      
      let macrosr1r2 = !macrolst in
      (*print_string ("Number of macros for r1/r2: "^(string_of_int (List.length macrosr1r2))^"\n");*)
      (*let file = open_out ("viewer/trees/r1r2_"^(string_of_int !counter)^".tex") in
      ProofTree.printTexMacros macrosr1r2 file;
      close_out file;
      counter := !counter + 1;*)
      macrolst := [];
      
      let findPermutation2 (mcrr1r2, mcrr1r2Constr) =   
        (* Get all models for this composed macro *)
        if !verbose then begin
          print_endline "Getting all models of some r1/r2";
          flush stdout
        end;
        let models = Constraints.getAllModels mcrr1r2Constr in
        (*print_string ("Number of models for r1/r2: "^(string_of_int (List.length models))^"\n");*)
        (* G TODO: Should this really fail? Maybe it should just return false
        and allow the outter method to choose another subset of leaves of r1*)
        if List.length models = 0 then failwith "Some r1/r2 is unsatisfiable."
        else begin
          let findPermutation3 mdl =
           
            let findPermutation4 (mr2, mr2Constr) = 
              
              (*let file = open_out ("viewer/trees/r2_"^(string_of_int !counter)^".tex") in
              ProofTree.printTexProof mr2 file;
              close_out file;
              counter := !counter + 1;*)
           
              let mr2cp = ProofTree.copy mr2 in
              let mr2ConstrCp = Constraints.copy mr2Constr in
              let openlvsr2 = ProofTree.getOpenLeaves mr2cp in
              (* Get all subsets of the leaves in macro-r2 *)
              let subsets = allnonemptysubsets openlvsr2 in
              (* if (List.length subsets) = 0 then failwith "Macro rule of r2 has no open leaves to apply r1."; *)
              
              if (List.length subsets) = 0 then failwith "r2 is an axiom, so the rules permute by definition";
           
              let findPermutation5 set =
                (* Apply r1 over a set of leaves of macro-r2 *)
                (*print_endline ("Applying r1 over "^(string_of_int (List.length set))^" leaves of r2.");*)
           
                (* Continuation function for recursive call of rmacros *)
                let rec cont n () = 
                  if n = 0 then begin
                    if !verbose then begin
                      print_endline "MACRO RULE FOR r2/r1";
                      ProofTree.printLeaves !macrorule;
                      Constraints.printConstraints !constrs;
                      flush stdout
                    end;
                    save_macro ()
                  end
                  else begin
                    let idx = (List.length set)-n in
                    initMacroFrom !macrorule (List.nth set idx) !constrs r1;
                    rmacro (cont (n-1))
                  end
                in
                ProofTree.mask mr2 mr2cp;
                macrorule := mr2cp;
                constrs := mr2ConstrCp;
                initMacroFrom !macrorule (List.hd set) !constrs r1;
                rmacro ( cont ((List.length set)-1) );
           
                let macrosr2r1 = !macrolst in
                (*print_string ("Number of macros for r2/r1: "^(string_of_int (List.length macrosr2r1))^"\n");*)
                macrolst := [];
                (*let macror2r1 = !macrorule in*)
           
                (*let file = open_out ("viewer/trees/r2r1_"^(string_of_int !counter)^".tex") in
                ProofTree.printTexMacros macrosr2r1 file;
                close_out file;
                counter := !counter + 1;*)
           
                let findPermutation6 (mcrr2r1, mcrr2r1Constrs) = 
                  (* Generate the ctx clauses for all the leaves of both trees *)
                  let leaves1 = ProofTree.getOpenLeaves mcrr1r2 in
                  let leaves2 = ProofTree.getOpenLeaves mcrr2r1 in
                  let ctxStr1 = genCtxFacts leaves1 1 0 in
                  let ctxStr2 = genCtxFacts leaves2 2 (List.length leaves1) in
                  let ctxStr = (ctxStr1^"\n\n"^ctxStr2) in
                  let okStr = genOkStr (List.length leaves1) ((List.length leaves1) + (List.length leaves2) - 1) in
           
                  (* Check if the macro-rule r2/r1 found satisfy all models of r1/r2 *)
                  (* G TODO: not checking if it satisfies all models, but only
                  one. Is it possible that one permutation satisfies one model
                  and another permutation satisfies another? Or is it the case
                  that all models must be satisfied by the same permutation? *)
                  if !verbose then begin
                    print_endline ("Checking if all "^(string_of_int (List.length models))^" models of r1/r2 are satisfiable by r2/r1");
                    flush stdout;
                  end;
                
                  (* Check if the model of r1/r2 is satisfied by this permutation *)
                  (*List.fold_right (fun e acc -> 
                    (Constraints.permCondition mcrr2r1Constrs ctxStr okStr e) && acc) models true*)
                  if Constraints.permCondition mcrr2r1Constrs ctxStr okStr mdl then begin
                    let file = open_out ("viewer/trees/permute_"^(string_of_int !counter)^".tex") in
                    ProofTree.printTex2Proofs mcrr1r2 mcrr2r1 file;
                    close_out file;
                    (*print_endline "************ This model has a permutation:";
                    print_endline mdl;*)
                    counter := !counter + 1;
                    true
                  end
                  else begin
                    let file = open_out ("viewer/trees/notpermute_"^(string_of_int !counter)^".tex") in
                    ProofTree.printTex2Proofs mcrr1r2 mcrr2r1 file;
                    close_out file;
                    (*print_endline "************ This model DOES NOT have a permutation:";
                    print_endline mdl;*)
                    counter := !counter + 1;
                    false
                  end

                in
                (* Some macro rule of r1 over a subset of r2 should be a permutation *)
                List.fold_right (fun mcrr2r1 acc -> findPermutation6 mcrr2r1 || acc) macrosr2r1 false
              in
              (* The application of r1 to _some_ of the subsets of mr2 should be a permutation *)
              List.fold_right (fun set acc -> findPermutation5 set || acc) subsets false
            in
            (* Some macro rule of r2 should be the basis of a permutation for r1/r2 *)
            List.fold_right (fun mr2 acc -> findPermutation4 mr2 || acc) macrosr2 false
          in
          (* All models of some macro rule of r1/r2 should correspond to a permutation *)
          List.fold_right (fun mdl acc -> findPermutation3 mdl && acc) models true
        end
      in
      (* All macro rules of r2 over one specific leaf of r1 should have a permutation *)
      List.fold_right (fun mr1r2 acc -> findPermutation2 mr1r2 && acc) macrosr1r2 true
    in
    (* Some application of r2 over some of the leaves of r1 should have a permutation *)
    List.fold_right (fun s acc -> findPermutation1 s || acc) subsets1 false
  in
  (* All macro rules from r1 should have a permutation *)
  List.fold_right (fun el acc -> findPermutation0 el && acc) macrosr1 true

(*
Para cada modelo M1 de r1/r2
procurar uma macro-rule/constraints/modelo (M2 U M1) de r2/r1
de tal forma que forall open sequents O of r2/r1, O pode ser provado dado que os
open sequents de r1/r2 sao provaveis.

forall r1/r2 exists r2/r1

Usar proveIf
Encontrar M2 de tal forma que proveIf seja verdade.

***** ALGORITHM ********

Let {c1, c2,..., cn} be the set of constraints of r1/r2. 
Run smodels, with each of theses constraints obtaining its models:
c1 -> m11, m12, ...
c2 -> m21, m22, ...
...

Let {d1, d2, ..., dm} be the set of constraints of r2/r1 (r1 over some subset of
the open leaves of r2).
For each of the models from r1/r2, run the file with the clauses:

mxy, di, ctxs (of both macro rules), provIf
  until it works with some di.

If it does not work for any di, try another subset of open leaves of r2 and
another set of constraints d.

If it worked for every mxy, conclude that it's permutable.

******* END ***********

For the introduction:
Usar SAT solvers para fazer reasoning sobre derivacoes automaticamente.

*)	


