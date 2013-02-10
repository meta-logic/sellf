(*****************************************)
(*                                       *)
(*  Constraint set for reasoning about   *)
(*  context variables                    *)
(*                                       *)
(*  Giselle Machado Reis                 *)
(*  2013                                 *)
(*                                       *)
(*****************************************)

open Term
open Prints
open SolverStr
open Unix
open Subexponentials
open Context

let i = ref 0;;

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

let create predlst = {
  lst = predlst
}

let union set1 set2 = create (set1.lst @ set2.lst)

(* Cross product between two sets of sets of constraints *)
let times set1 set2 = List.concat (List.map (fun cst1 ->
  List.map (fun cst2 -> union cst1 cst2) set2
) set1)

let copy cst = create cst.lst

let requireIn f subexp ctx =
  let index = ContextSchema.getIndex ctx subexp in
  create [REQIN(f, (subexp, index))]

let remove f subexp oldctx newctx = 
  let oldindex = ContextSchema.getIndex oldctx subexp in
  let newindex = ContextSchema.getIndex newctx subexp in
  create [REMOVED(f, (subexp, oldindex), (subexp, newindex))]

let insert f subexp oldctx newctx = 
  let oldindex = ContextSchema.getIndex oldctx subexp in
  let newindex = ContextSchema.getIndex newctx subexp in
  let middleindex = newindex - 1 in
  create [ELIN(f, (subexp, middleindex));
  UNION((subexp, oldindex), (subexp, middleindex), (subexp, newindex))]

let empty subexp ctx = 
  let index = ContextSchema.getIndex ctx subexp in
  create [EMP(subexp, index)]

(* Creates the union constraints of linear contexts of newctx1 and newctx2
  resulting in contexts of ctx *)
let split ctx newctx1 newctx2 =
  let contexts = ContextSchema.getContexts ctx in
  let cstrlst = List.fold_right (fun (s, i) acc -> 
    let i1 = ContextSchema.getIndex newctx1 s in
    let i2 = ContextSchema.getIndex newctx2 s in
    if (i1 != i2) then
      UNION((s, i1), (s, i2), (s, i)) :: acc
    else acc
  ) contexts [] in
  create cstrlst

(* Creates the emptiness constraints for the bang rule *)
(* GR TODO: check if this creates the constraint that $gamma should be empty *)
let bang ctx subexp = 
  let contexts = ContextSchema.getContexts ctx in
  let cstrlst = List.fold_right (fun (s, i) acc ->
    if s = subexp || (greater_than s subexp) then acc
    else EMP(s, i) :: acc
  ) contexts [] in
  create cstrlst

(* Several sets of constraints are created and a list of constraint sets is
returned *)
let initial ctx f = 
  let contexts = ContextSchema.getContexts ctx in
  (* Suppose the dual of f is in s, generates all the constraints *)
  let isHere (sub, i) dualf = 
    let c1 = match type_of sub with
    | LIN | AFF -> ELIN(dualf, (sub, i))
    | UNB | REL -> MCTX(dualf, (sub, i))
    in
    let empty = List.fold_right (fun (s, i) acc ->
      if s != sub then begin match type_of s with
        | LIN | AFF -> EMP(s, i) :: acc
        | UNB | REL -> acc
      end else acc
    ) contexts []
    in
    c1 :: empty
  in
  let cstrs = List.fold_right (fun c acc ->
    ( isHere c (deMorgan(NOT(f))) ) :: acc 
  ) contexts [] in
  List.map (fun set -> create set) cstrs
  
let ctxToTex (s, i) = 
  let news = remSpecial s in
  ("$\\Gamma_{"^news^"}^{"^(string_of_int i)^"}$")

let ctxToStr (s, i) = 
  let news = remSpecial s in
  ""^news^""^(string_of_int i)^""

(* GR TODO check if I cannot reduce the redundancy of these printing methods... *)
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
  | REQIN (t, c) -> 
    Printf.fprintf out "\\item requiredIn(%s, %s)\n" (termToTexString t) (ctxToTex c)
  | REMOVED (t, c1, c2) -> 
    Printf.fprintf out "\\item removed(%s, %s, %s)\n" (termToTexString t) (ctxToTex c1) (ctxToTex c2)

let rec printTexConstraints csts out = 
  Printf.fprintf out "\\begin{itemize}.\n";
  List.iter (fun c -> printTexConstraint c out) csts.lst;
  Printf.fprintf out "\\end{itemize}.\n"

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
  | REQIN (t, c) -> 
    Printf.printf "requiredIn(%s, %s)\n" (termToTexString t) (ctxToTex c);
    flush (out_channel_of_descr stdout)
  | REMOVED (t, c1, c2) -> 
    Printf.printf "removed(%s, %s, %s)\n" (termToTexString t) (ctxToTex c1) (ctxToTex c2);
    flush (out_channel_of_descr stdout)

let printConstraints csts = 
  let i = ref 1 in
  List.iter (fun c -> 
    print_string ("-- Constraint set "^(string_of_int !i)^":\n");
    i := !i + 1;
    printConstraint c
  ) csts.lst

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
  | REQIN (t, c) -> 
    Printf.fprintf out "requiredIn(\"%s\", %s)\n" (termToTexString t) (ctxToTex c)
  | REMOVED (t, c1, c2) -> 
    Printf.fprintf out "removed(\"%s\", %s, %s)\n" (termToTexString t) (ctxToTex c1) (ctxToTex c2)

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

(* GR TODO reorganize the file generation methods... *)

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

