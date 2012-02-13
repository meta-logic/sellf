open Term
open Structs
open Prints
open SolverStr
open Unix

let i = ref 0;;

module Constraints =
  struct
    type ctx = string * int
    type cstr = 
(*      | FAIL (* G: I believe this is not used and we can drop it. *)*)
      | MCTX of terms * ctx
      | ELIN of terms * ctx
      | EMP of ctx
(*      | EQF of terms * terms (* G: I believe this is not used and we can drop
it. *)*)
(*      | EQCTX of ctx list * ctx list (* G: I believe this is not used and we
can drop it. *)*)
      | UNION of ctx * ctx * ctx
      | ADDFORM of terms * ctx * ctx
     
    type constraints = {
      (* The constraints is a set of sets. *)
      mutable lst : cstr list list;
    }

    let create () = {
        lst = [[]]
    }

    let setConstraints cst clst = cst.lst <- clst

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

    let clear cst = cst.lst <- [[]]
    
    (* When a new constraint is added, it should be added in every set *)
    (*let add csts c = csts.lst <- c :: csts.lst ;;*)

    (* Combine every previous set of constraints with each new set *)
    let rec add csts newlst = 
      let rec addaux a b = match b with
        | [] -> []
        | c :: tl -> (List.map (fun l -> c @ l) csts.lst) @ addaux a tl
      in csts.lst <- addaux csts newlst
    ;;

    let printTexConstraint c out = match c with
      (*| FAIL -> Printf.fprintf out "\\item Fail.\n\n"*)
      | MCTX (t, c) -> 
        Printf.fprintf out "\\item mctx("; 
        print_term_tex out t;
        let cstr = ctxToTex c in
        Printf.fprintf out ", %s)\n" cstr;
      | ELIN (t, c) ->
        Printf.fprintf out "\\item elin("; 
        print_term_tex out t;
        let cstr = ctxToTex c in
        Printf.fprintf out ", %s)\n" cstr;
      | EMP (c) -> 
        let cstr = ctxToTex c in
        Printf.fprintf out "\\item emp(%s).\n" cstr
      (*| EQF (t1, t2) -> Printf.fprintf out "\\item eqf.\n"
      | EQCTX (l1, l2) -> Printf.fprintf out "\\item eqctx.\n"*)
      | UNION (c1, c2, c3) -> 
        let c1str = ctxToTex c1 in
        let c2str = ctxToTex c2 in
        let c3str = ctxToTex c3 in
        Printf.fprintf out "\\item union(%s, %s, %s).\n" c1str c2str c3str 
      | ADDFORM (t, c1, c2) -> 
        Printf.fprintf out "\\item addform("; 
        print_term_tex out t;
        let c1str = ctxToTex c1 in
        let c2str = ctxToTex c2 in
        Printf.fprintf out ", %s, %s).\n" c1str c2str 

    let printTexConstraints csts out = 
      let rec printCstLst lst out = match lst with
        | [] -> Printf.fprintf out "\\item End of constraints.\n"
        | h::t -> printTexConstraint h out; printCstLst t out
      in List.iter (fun l -> printCstLst l out) csts.lst

    let printConstraint c = match c with
      (*| FAIL -> print_string "- Fail.\n"; flush stdout*)
      | MCTX (t, c) -> 
        print_string "mctx( "; 
        print_term t;
        let cstr = ctxToStr c in
        print_string (", "^cstr^" )\n");
        flush (out_channel_of_descr stdout)
      | ELIN (t, c) ->
        print_string "elin( "; 
        print_term t;
        let cstr = ctxToStr c in
        print_string (", "^cstr^" )\n");
        flush (out_channel_of_descr stdout)
      | EMP (c) -> 
        let cstr = ctxToStr c in
        print_string ("emp( "^cstr^" ).\n");
        flush (out_channel_of_descr stdout)
      (*| EQF (t1, t2)   -> print_string "- eqf.\n";
        flush out_channel_of_descr stdout  
      | EQCTX (l1, l2  ) -> print_string "- eqctx.\n";
        flush out_channel_of_descr stdout  *)
      | UNION (c1, c2, c3) -> 
        let c1str = ctxToStr c1 in
        let c2str = ctxToStr c2 in
        let c3str = ctxToStr c3 in
        print_string ("union( "^c1str^", "^c2str^", "^c3str^" ).\n");
        flush (out_channel_of_descr stdout)
      | ADDFORM (t, c1, c2) -> 
        print_string "addform( "; 
        print_term t;
        let c1str = ctxToStr c1 in
        let c2str = ctxToStr c2 in
        print_string (", "^c1str^", "^c2str^" ).\n");
        flush (out_channel_of_descr stdout)

    let printConstraints csts = 
      let i = ref 1 in
      let rec printCstLst lst = match lst with
        | [] -> print_string "\n"
        | h::t -> printConstraint h; printCstLst t
      in List.iter (fun l -> 
          print_string ("-- Constraint set "^(string_of_int !i)^":\n");
          i := !i + 1;
          printCstLst l) csts.lst

    (* Print constraints to a file *)
    let printfConstraint c out = match c with
      | MCTX (t, c) -> 
        Printf.fprintf out "mctx(\""; 
        printf_term out t;
        let cstr = ctxToStr c in
        Printf.fprintf out "\", %s).\n" cstr;
      | ELIN (t, c) ->
        Printf.fprintf out "elin(\""; 
        printf_term out t;
        let cstr = ctxToStr c in
        Printf.fprintf out "\", %s).\n" cstr;
      | EMP (c) -> 
        let cstr = ctxToStr c in
        Printf.fprintf out "emp(%s).\n" cstr
      | UNION (c1, c2, c3) -> 
        let c1str = ctxToStr c1 in
        let c2str = ctxToStr c2 in
        let c3str = ctxToStr c3 in
        Printf.fprintf out "union(%s, %s, %s).\n" c1str c2str c3str 
      | ADDFORM (t, c1, c2) -> 
        Printf.fprintf out "addform(\""; 
        printf_term out t;
        let c1str = ctxToStr c1 in
        let c2str = ctxToStr c2 in
        Printf.fprintf out "\", %s, %s).\n" c1str c2str 

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
    let genSolverInput constraints n = 
      let i = ref 0 in
      List.iter (fun l ->
        i := !i + 1;
        let name = "const_set_"^(string_of_int n)^"_"^(string_of_int !i) in
        genFile l name
      ) constraints.lst

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
    let getAllModels c = List.flatten (List.fold_right (fun e acc -> getModels e :: acc) c.lst [])

    (* Checks if some set of constraints and the model m satisfy the
    permutability condition *)
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

  end
;;


