open Term
open Prints
open SolverStr
open Unix
open Subexponentials
open Context

let i = ref 0;;
(* TODO: rewrite the commented out methods to the current type *)
(*module Constraints =
  struct*)

    type ctx = string * int
    type constraintpred = 
      | MCTX of terms * ctx
      | ELIN of terms * ctx
      | EMP of ctx
      | UNION of ctx * ctx * ctx
      | ADDFORM of terms * ctx * ctx
      | REQIN of terms * ctx
      | REMOVED of terms * ctx * ctx
     
    type constraintset = {
      mutable lst : constraintpred list;
    }

    let create () = {
      lst = []
    }

    let add cst newc = cst.lst < cst.lst @ newc

    let setConstraints cst clst = cst.lst <- clst

    let requireIn f subexp ctx =
      let index = ContextSchema.getIndex ctx subexp in
      REQIN(f, (subexp, index))

    let remove f subexp oldctx newctx = 
      let oldindex = ContextSchema.getIndex oldctx subexp in
      let newindex = ContextSchema.getIndex newctx subexp in
      REMOVED(f, (subexp, oldindex), (subexp, newindex))

    (*
    let copy cst = let cp = create () in
      let rec copylist l = match l with
        | [] -> []
        | h::t -> match h with
          (*| FAIL -> FAIL :: copylist t*)
          | MCTX (tm, c) -> MCTX(tm,c) :: copylist t
          | ELIN (tm, c) -> ELIN(tm,c) :: copylist t
          | EMP (c) -> EMP(c) :: copylist t
          (*| EQF (t1, t2) -> EQF(t1,t2) :: copylist t*)
          (*| EQCTX (cl1, cl2) -> EQCTX(cl1, cl2) :: copylist t*)
          | UNION (c1, c2, c3) -> UNION(c1, c2, c3) :: copylist t
          | ADDFORM (f, c1, c2) -> ADDFORM(f, c1, c2) :: copylist t
      in
      setConstraints cp (List.map (fun l -> copylist l) cst.lst); cp
    *)

    let clear cst = cst.lst <- []
    
    (* Combine every previous set of constraints with each new set *)
    (*
    let rec add csts newlst = 
      let rec addaux a b = match b with
        | [] -> []
        | c :: tl -> (List.map (fun l -> c @ l) csts.lst) @ addaux a tl
      in csts.lst <- addaux csts newlst
    ;;
    *)

    let ctxToTex (s, i) = 
      let news = remSpecial s in
      ("$\\Gamma_{"^news^"}^{"^(string_of_int i)^"}$")
 
    let ctxToStr (s, i) = 
      let news = remSpecial s in
      ""^news^""^(string_of_int i)^""

    let printTexConstraint c out = match c with
      | MCTX (t, c) -> 
        Printf.fprintf out "\\item mctx(%s, %s)\n"  (termToTexString t) (ctxToTex c)
      | ELIN (t, c) ->
        Printf.fprintf out "\\item elin(%s, %s)\n" (termToTexString t) (ctxToTex c)
      | EMP (c) -> 
        Printf.fprintf out "\\item emp(%s).\n" (ctxToTex c)
      | UNION (c1, c2, c3) -> 
        Printf.fprintf out "\\item union(%s, %s, %s).\n" (ctxToTex c1) (ctxToTex c2) (ctxToTex c3)
      | ADDFORM (t, c1, c2) -> 
        Printf.fprintf out "\\item addform(%s, %s, %s)\n" (termToTexString t) (ctxToTex c1) (ctxToTex c2)

    (*
    let printTexConstraints csts out = 
      let rec printCstLst lst out = match lst with
        | [] -> Printf.fprintf out "\\item End of constraints.\n"
        | h::t -> printTexConstraint h out; printCstLst t out
      in List.iter (fun l -> printCstLst l out) csts.lst
    *)

    let printConstraint c = match c with
      | MCTX (t, c) -> 
        Printf.printf "mctx(%s, %s)\n"  (termToTexString t) (ctxToTex c);
        flush (out_channel_of_descr stdout)
      | ELIN (t, c) ->
        Printf.printf "elin(%s, %s)\n" (termToTexString t) (ctxToTex c);
        flush (out_channel_of_descr stdout)
      | EMP (c) -> 
        Printf.printf "emp(%s).\n" (ctxToTex c);
        flush (out_channel_of_descr stdout)
      | UNION (c1, c2, c3) -> 
        Printf.printf "union(%s, %s, %s).\n" (ctxToTex c1) (ctxToTex c2) (ctxToTex c3);
        flush (out_channel_of_descr stdout)
      | ADDFORM (t, c1, c2) -> 
        Printf.printf "addform(%s, %s, %s)\n" (termToTexString t) (ctxToTex c1) (ctxToTex c2);
        flush (out_channel_of_descr stdout)

    (*
    let printConstraints csts = 
      let i = ref 1 in
      let rec printCstLst lst = match lst with
        | [] -> print_string "\n"
        | h::t -> printConstraint h; printCstLst t
      in List.iter (fun l -> 
          print_string ("-- Constraint set "^(string_of_int !i)^":\n");
          i := !i + 1;
          printCstLst l) csts.lst
    *)

    (* Print constraints to a file *)
    let printfConstraint c out = match c with
      | MCTX (t, c) -> 
        Printf.fprintf out "mctx(\"%s\", %s)\n"  (termToTexString t) (ctxToTex c)
      | ELIN (t, c) ->
        Printf.fprintf out "elin(\"%s\", %s)\n" (termToTexString t) (ctxToTex c)
      | EMP (c) -> 
        Printf.fprintf out "emp(%s).\n" (ctxToTex c)
      | UNION (c1, c2, c3) -> 
        Printf.fprintf out "union(%s, %s, %s).\n" (ctxToTex c1) (ctxToTex c2) (ctxToTex c3)
      | ADDFORM (t, c1, c2) -> 
        Printf.fprintf out "addform(\"%s\", %s, %s)\n" (termToTexString t) (ctxToTex c1) (ctxToTex c2)

    let rec printConstrList lst out = match lst with
      | [] -> ()
      | hd::tl -> printfConstraint hd out; printConstrList tl out

    let genFile cList name = 
      let file = open_out ("solver/"^name^".in") in
      Printf.fprintf file "%s" description;
      Printf.fprintf file "%s" union_clauses_set;
      Printf.fprintf file "%s" elin_clauses_set;
      Printf.fprintf file "%s" emp_clauses_set;
      Printf.fprintf file "%s" mctx_clauses_set;
      Printf.fprintf file "%s" addform_clauses_set;
      Printf.fprintf file "%s" aux_clauses_set;
      printConstrList cList file;
      close_out file

    let subexpOrdStr () = Hashtbl.fold (fun key data acc ->
      "geq("^(remSpecial data)^", "^(remSpecial key)^").\n"^acc
    ) subexOrdTbl ""
    let reflSubexpRel () = Hashtbl.fold (fun key data acc -> 
      "geq("^(remSpecial key)^", "^(remSpecial key)^").\n"^acc
    ) subexTpTbl ""

    let genPermFile cList ctxStr okStr model name =  
      let file = open_out ("solver/"^name^".in") in
      Printf.fprintf file "%s" description;
      Printf.fprintf file "%s" union_clauses_set;
      Printf.fprintf file "%s" elin_clauses_set;
      Printf.fprintf file "%s" emp_clauses_set;
      Printf.fprintf file "%s" mctx_clauses_set;
      Printf.fprintf file "%s" addform_clauses_set;
      Printf.fprintf file "%s" aux_clauses_set;
      Printf.fprintf file "%s" proveIf_clauses;
      Printf.fprintf file "%s\n" okStr;
      Printf.fprintf file "%s" (reflSubexpRel ());
      Printf.fprintf file "%s" (subexpOrdStr ());
      Printf.fprintf file "%s" ctxStr;
      Printf.fprintf file "%s\n" model;
      printConstrList cList file;
      close_out file

    (* One file for each set of constraints *)
    (*
    let genSolverInput constraints n = 
      let i = ref 0 in
      List.iter (fun l ->
        i := !i + 1;
        let name = "const_set_"^(string_of_int n)^"_"^(string_of_int !i) in
        genFile l name
      ) constraints.lst
    *)

    (* Get the models from one set of constraints *)
    (* This function will return a list of models. These models are represented
    as strings which are the true predicated in the format of facts (e.g.
    "pred(a). pred(b)." *)
    let getModels cList = 
      genFile cList "temp";
      let sedStr = " | sed \"s/{//\" | sed \"s/}/./\" | sed \"s/[a-zA-Z]*\\(\\), /. /g\" " in
      let channel = Unix.open_process_in ("dlv -silent solver/temp.in"^sedStr) in
      let rec readModel input = try match input_line input with
        | str -> str :: readModel input
        with End_of_file -> let _ = Unix.close_process_in channel in []
      in
      readModel channel
      
    (* Get all the models from all the sets of constraints *)
    (*
    let getAllModels c = List.flatten (List.fold_right (fun e acc -> getModels e :: acc) c.lst [])
    *)
    
    (* Checks if some set of constraints and the model m satisfy the
    permutability condition *)
    (*
    let permCondition cstrs ctxStr okStr mdl =
      let lst = cstrs.lst in
      let rec condition mdl cList = match cList with
        | [] -> false
        | c :: tl ->
          genPermFile c ctxStr okStr mdl ("temp_perm"^(string_of_int !i));
          let channel = Unix.open_process_in ("dlv -silent solver/temp_perm"^(string_of_int !i)^".in") in
          i := !i + 1;
          try match input_line channel with
            | _ -> let _ = Unix.close_process_in channel in 
              (*print_endline "Some model is satisfiable."; flush
              (out_channel_of_descr stdout)*) (); 
              true
            with End_of_file -> let _ = Unix.close_process_in channel in condition mdl tl
      in
      condition mdl lst
    *)

  (*end*)
;;


