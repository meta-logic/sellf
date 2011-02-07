open Term
open Structs
open Unify

let unify = 
  let module Unify = 
    Unify.Make ( struct
      let instantiatable = Term.LOG
      let constant_like = Term.EIG
    end )
  in Unify.pattern_unify

(* Solves an arithmetic expression *)
let rec solve_exp e = match e with
  | INT (x) -> x
  | VAR v -> 1(* Infer the variable value?? *)
  | PLUS (x, y) -> (solve_exp x) + (solve_exp y)
  | MINUS (x, y) -> (solve_exp x) - (solve_exp y)
  | TIMES (x, y) -> (solve_exp x) * (solve_exp y)
  | DIV (x, y) -> (solve_exp x) / (solve_exp y)
  | PTR {contents = T t} -> solve_exp t
  | PTR {contents = V t} when t.tag = Term.LOG -> 
      print_string "ERROR: Cannot handle comparisons with logical variables.";  print_term e; print_newline (); 0
  | bla -> print_string "[ERROR] Unexpected term in a comparison: "; print_term bla; print_newline (); 0

(* Solves an arithmetic comparisson *)
let solve_cmp c e1 e2 = 
  let n1 = solve_exp e1 in 
  let n2 = solve_exp e2 in
    match c with
      | EQ -> n1 = n2
      | LESS -> n1 < n2
      | GEQ -> n1 >= n2        
      | GRT -> n1 > n2
      | LEQ -> n1 <= n2
      | NEQ -> n1 != n2
;;

(* Creating a new subexponential *)
let new_subexp s = 
  try match Hashtbl.find subexTpTbl s with
  | _ -> ()
  with Not_found -> Hashtbl.add subexTpTbl s (LIN); Hashtbl.add !context s [] ;;
  
(* Verifying if a subexponential is empty *)
let empty s = List.length (Hashtbl.find !context s) == 0 ;;

(* Checks if a subexponential s1 > s2 *)

let rec bfs root queue goal = match queue with
  | [] -> false
  | h :: t when h = root -> failwith "Circular dependency on subexponential order."
  | h :: t when h = goal -> true
  | h :: t -> bfs root (t @ Hashtbl.find_all subexOrdTbl h) goal
;;

let greater_than s1 s2 = bfs s2 (Hashtbl.find_all subexOrdTbl s2) s1 ;;

(* END Checks if a subexponential s1 > s2 *)

(* Checks if bang rule can be applied with subexponential s *)
let rec cb s idxs = match idxs with
  | [] -> true
  | i::t  -> 
    if i == "$gamma" then cb s t
    else
      try match Hashtbl.find subexTpTbl i with
        | UNB | AFF -> cb s t (* This can suffer weakening, go on... *)
        | REL | LIN -> (try match Hashtbl.find !context i with
          | [] -> cb s t
          | _ -> if i = s || (greater_than i s) then cb s t (* This subexp can have formulas in it. *)
                 else (print_string ("Failed in bang rule: "^i^"  "^s^"\n"); false)
          with Not_found -> cb s t ) (* This means that this subexp is empty *)
      with Not_found -> print_string ("[ERROR] Subexponential "^i^" has no type defined."); false
;;

let condition_bang s = let idxs = keys !context in cb s idxs;;

(* Removes all formulas from a subexponential *)
let remove_all s = Hashtbl.remove !context s; Hashtbl.add !context s [] ;;

(* Operation k <l for K context *)
let k_less_than s = Hashtbl.iter (fun idx forms -> if idx != "$gamma" && not (idx = s) && not (greater_than idx s) then begin print_string ("Removing from "^idx^" in k_less_than "^s^"\n"); remove_all idx end) !context;;

(* Checks whether or not a subexponential can suffer weakening *)
let weak i = try match Hashtbl.find subexTpTbl i with
  | UNB | AFF -> true
  | REL | LIN -> false
  with Not_found -> print_string ("[ERROR] Subexponential "^i^" has no type defined."); false

(* Returns a list with all the formulas that cannot suffer weakening *)
(* FIXME: this dummy parameter was used so the method was called... *)
let weakenable dummy = Hashtbl.fold (fun s forms l -> 
    (*print_string s;
    print_list_terms forms;*)
    if not (weak s) then 
    begin
      forms@l
    end
    else l) !context [] ;;

(* Checks whether K context is empty on the subexponentials that cannot suffer weakening *)
(* FIXME: this dummy parameter was used so the method was called... *)
let empty_nw dummy =
  match (List.length (weakenable ())) with
    | 0 -> print_string "Weakable subexponential"; true
    | n -> print_string "Non-weakenable context is not empty.\n"; 
      print_string "Tensor is set to: "; 
      print_int !tensor; print_newline(); 
      false
;;

(* Saves the state for backtracking later (called whenever a non-deterministic
 * choice is made, i.e., when a positive formula or atom is focused on) *)
let save_state form tp pos =  
  let ctx_cp = Hashtbl.copy !context in
  let cls_cp = Hashtbl.copy !clausesTbl in
  let dt = DATA(!goals, !positives, !atoms, ctx_cp, cls_cp) in
  let st = STATE(dt, form, tp, pos) in
  Stack.push st !states
;;

let reset dt = match dt with
  | DATA (g, p, a, c, ct) ->
    goals := g;
    positives := p;
    atoms := a;
    context := Hashtbl.copy c;
    clausesTbl := Hashtbl.copy ct;
;;


(* Functions to substitute a variable in a formula *)
let rec apply_ptr f = match f with
  | ABS(s, i, t) ->
      varid := !varid + 1;
      let newVar = V {str = s; id = !varid; tag = Term.LOG; ts = 0; lts = 0} in
      let ptr = PTR {contents = newVar} in
      (*print_string "\nApplying "; print_term ptr; print_string " to "; print_term (ABS(s, i, t)); print_newline ();*)
      let newf = Norm.hnorm (APP(ABS(s, i, t), [ptr])) in
      apply_ptr newf
  | x -> x

(* [END] Functions to transform variables to pointers in a formula *)

let unifies f1 f2 =
  let fp1 = apply_ptr f1 in
  let fp2 = apply_ptr f2 in
    print_string "****** Unifying (head of first with second): \n"; print_term fp1; print_newline (); print_term fp2;
    print_newline ();
    match fp1, fp2 with
    | LOLLI(CONS(s), head, body), (PRED (str2, terms2)) -> 
      begin match head with
      | (PRED(str1, terms1)) ->
          begin try match unify terms1 terms2 with
            | () ->
              print_string "******* After unification: \n"; print_term fp1; print_newline ();
              print_term fp2; print_newline ();
              (fp1, fp2)
            with _ ->  failwith "Unification not possible."
                           (*begin match terms1, terms2 with 
                            | APP(CONS("c"), _), APP(CONS("c"), _) -> failwith "Unification not possible."
                            end*)
        end
      | _ -> failwith "Head of a clause not a predicate."
      end
    | _ -> failwith "Formulas not compatible (should be lolli and pred)."
;;

(* Solves a LL formula *)

(* Classic version *)
(* FIXME: find a way to remove all the dummy parameters *)
(* FIXME: this would yield true for the empty sequent... *)
let rec solve dummy = 
  if solve_neg () then begin 
    if (List.length !positives) != 0 then
      save_state (List.hd !positives) POS 0;
    if solve_pos () then begin
      if (List.length !atoms) != 0 then
        save_state (List.hd !atoms) ATM 0;
      solve_atm () 
    end
    else false
  end
  else false

and solve_neg dummy = (*match !goals with*)
try
let form = List.hd !goals in
let t = List.tl !goals in
match Term.observe form with

  (* Negative formulas *)

  (* Put f1 in subexponential s of the context, put (f1, s) in head f1 of clausesTbl and continue with f2 *)
  (* If s is $gamma (linear implication), decompose f1 up to negatives and atoms and put these formulas in $gamma *)
  (* Otherwise, put f1 in subexponential s and f1 :- f2 in the clauses hash 
  (Note that f1 is either an atom or -o if it's in a subexponential.) *)
  | LOLLI (sub, f1, f2) -> (match (Term.observe sub) with
    | CONS("$gamma") -> 
      let terminate = ref true in
      let rec decompose f = match f with
        | TENSOR (form1, form2) -> decompose form1; decompose form2
        | BANG (s, form) | HBANG (s, form) -> ( match form, (Term.observe s) with
          | PRED(str,terms), CONS(sub) -> 
            add_ctx (LOLLI (CONS(sub), PRED(str,terms), ONE)) sub;
            add_cls (LOLLI (CONS(sub), PRED(str,terms), ONE))
          | LOLLI(CONS(se), fl1, fl2), CONS(sub) ->
            add_ctx (LOLLI(CONS(se), fl1, fl2)) se;
            add_cls (LOLLI(CONS(se), fl1, fl2))
          | _ -> failwith "Lolli head error or unitialized subexponential"
        )
        | PRED (str, terms) ->
          add_lin (LOLLI (CONS("$gamma"), PRED(str,terms), ONE));
          add_cls (LOLLI (CONS("$gamma"), PRED(str,terms), ONE))
        | COMP(ct, t1, t2) -> if solve_cmp ct t1 t2 then () 
          else terminate := true
        | x -> add_lin x (* Negative formula or atom *)
      in decompose f2; goals := (f1 :: t); if !terminate then true else solve_neg ()
    | CONS(subexp) -> ( match f2 with
      (* TODO: Should I check the cases for equalities here also? What about the rest of the cases? *)
      | PRED(str,terms) ->
        add_ctx (LOLLI (CONS(subexp), PRED(str,terms), ONE)) subexp;
        add_cls (LOLLI (CONS(subexp), PRED(str,terms), ONE));
        goals := (f1 :: t); solve_neg ()
      | LOLLI(sub2, fl1, fl2) ->
        begin match sub2 with
          | CONS(se) ->
            add_ctx (LOLLI(CONS(se), fl1, fl2)) se;
            add_cls (LOLLI(CONS(se), fl1, fl2)); 
            goals := (f1 :: t); solve_neg ()
          | _ -> failwith "Unitialized subexponential while solving negative formulas."
        end
      | _ -> failwith "Lolli head error"
    )
  )
  (* Solves f1 and f2 with the same context *)
  | WITH (f1, f2) -> (
    let orig_context = !context in
    let orig_states = !states in
    let orig_clauses = !clausesTbl in
    goals := (f1 :: t);
    if solve_neg () then 
    (
      context := orig_context;
      states := orig_states;
      clausesTbl := orig_clauses;
      goals := (f2 :: t);
      solve_neg ()
    )
    else false
  )
  | FORALL (s, i, f) ->
      varid := !varid + 1;
      let new_var = VAR ({str = s; id = !varid; tag = Term.EIG; ts = 0; lts = 0}) in
      (*let newf = subst_var new_var f in*)
      let newf = Norm.hnorm (APP (ABS (s, 1, f), [new_var])) in
      goals := newf :: t;
      solve_neg ()
  | TOP -> true

  | NEW (s, t1) -> 
      varid := !varid + 1;
      let string_sub = "NSUBEXP"^(string_of_int !varid) in
      let new_cons = CONS string_sub in
      let newf = Norm.hnorm (APP (ABS (s, 1, t1), [new_cons])) in
      new_subexp s;
      goals := newf :: t;
      solve_neg ()

  (* Positive formulas *)

  | TENSOR (f1, f2) -> add_pos (TENSOR (f1, f2)); goals := t; solve_neg ()
  | BANG (s, f) -> add_pos (BANG (s, f)); goals := t; solve_neg ()
  | HBANG (s, f) -> add_pos (HBANG (s, f)); goals := t; solve_neg ()
  | ONE -> add_pos ONE; goals := t; solve_neg ()
  | COMP (ct, t1, t2) -> add_pos (COMP (ct, t1, t2)); goals := t; solve_neg ()

  (* Atoms *)
  | PRED(str, terms) -> add_atm (PRED(str, terms)); goals := t; solve_neg ()

  | EQU (str, n, trm) -> print_string "Not solving term equality yet."; false
  | CUT -> print_string "What should I do when encounter a cut?"; false
  | CONS(str) -> add_atm (PRED (str, CONS(str))); goals := t; solve_neg ()
  | APP(head, arg1) -> 
    begin
      match (Norm.hnorm (APP(head, arg1))) with
      | CONS(str) -> add_atm (PRED (str, CONS(str))); goals := t; solve_neg ()
      | APP(CONS(str3), arg2) -> add_atm (PRED (str3, APP(CONS(str3), arg2))); 
          goals := t; solve_neg ()
    end

  | h -> print_term h; failwith " Solving not implemented for this case."

  (* Empty list, solve the positive formulas now *)
    
  (*| [] -> true *)
  with 
    | Failure "hd" -> true
    (*| Match_failure _ -> true*)


and solve_pos dummy = (*match !positives with*)
try
let form = List.hd !positives in
let t = List.tl !positives in
match Term.observe form with

  (* If a negative formulas was found, put it in goals list and call solve again (back to async phase) *)
     
  | LOLLI (sub, f1, f2) -> 
    begin 
      match Term.observe sub with
      | CONS(s) -> 
        add_goals (LOLLI (sub, f1, f2)); 
        if solve_neg () then begin
          positives := t;
        if (List.length !positives) != 0 then
          save_state (List.hd !positives) POS 0;
          solve_pos ()
        end
        else backtrack ()
      | _ -> failwith "Unitialized subexponential while solving postive formulas."
   end 
  | WITH (f1, f2) -> 
    add_goals (WITH (f1, f2));
    if solve_neg () then begin
      positives := t;
      if (List.length !positives) != 0 then
        save_state (List.hd !positives) POS 0;
      solve_pos ()
    end
    else backtrack ()
  | FORALL (s, i, f) -> 
    add_goals (FORALL (s, i, f));
    if solve_neg () then begin
      positives := t;
      if (List.length !positives) != 0 then
        save_state (List.hd !positives) POS 0;
      solve_pos ()
    end
    else backtrack ()
  | TOP -> 
    add_goals TOP;
    if solve_neg () then begin
      positives := t;
      if (List.length !positives) != 0 then
        save_state (List.hd !positives) POS 0;
      solve_pos ()
    end
    else backtrack ()
  | NEW (s,t1) -> 
    add_goals (NEW (s,t1));
    if solve_neg () then begin
      positives := t;
      if (List.length !positives) != 0 then
        save_state (List.hd !positives) POS 0;
      solve_pos ()
    end
    else backtrack ()


  (* Positive formulas *)

  | TENSOR (f1, f2) ->
    let orig_states = !states in
      add_goals f1;
      positives := t;
      tensor := !tensor + 1;
      if solve () then (
        print_string "Solved the first formula from the tensor.\n";
        states := orig_states;
        add_goals f2;
        print_string "Solve now: "; print_term f2; print_newline (); flush stdout;
        tensor := !tensor - 1;
        if solve () then
         solve_pos ()
        else backtrack ()
      )
      else backtrack ()
  
  | BANG (sub, f) -> 
    begin (*print_string "Context before applying bang rule: \n"; print_hashtbl !context; print_newline ();*)
      match Term.observe sub with
      | CONS(s) -> 
          if condition_bang s then begin
          (*print_string "Context before k_less_than: \n"; print_hashtbl !context; print_newline ();*)
          k_less_than s; 
          (*print_string "Context after k_less_than: \n"; print_hashtbl !context; print_newline ();*)
          positives := (f :: []); 
          solve_pos ()
          (* I will not save the state here. If f is proved, I would have to make
            positives := []; save_state ...; solve_pos ()
            which would yield true anyway
          *)
        end
        else backtrack ()
      | _ -> failwith "Not expected subexponential while solving positive formulas."
    end

  | HBANG (sub, f) -> begin
    match Term.observe sub with
      | CONS (s) -> ( try match Hashtbl.find !context s with
        | [] -> print_string "Solved hbang.\n"; positives := (f :: []); solve_pos ()
        | _ -> backtrack ()
        with Not_found -> print_string "Solved hbang.\n"; positives := (f :: []); solve_pos ()
      )
      | _ -> failwith "Not expected subexponential while solving positive formulas."
    end

  | ONE -> 
    (* If I am solving a tensor, I can leave the checking of empty context for the next formula. *)
    if !tensor > 0 || empty_nw () then begin
      positives := t;
      if (List.length !positives) != 0 then
        save_state (List.hd !positives) POS 0;
      solve_pos ()
    end    
    else backtrack ()

  | COMP (ct, t1, t2) -> 
    if (solve_cmp ct t1 t2) then begin
      positives := t;
      if (List.length !positives) != 0 then
        save_state (List.hd !positives) POS 0;
      solve_pos ()
    end    
    else backtrack ()

  (* Atoms *)
  | PRED (str, terms) -> add_atm (PRED (str, terms)); positives := t; solve_pos ()

  | EQU (str, n, trm) -> print_string "Not solving term equality yet."; false
  | CUT -> print_string "What should I do when encounter a cut?"; false
  | CONS(str) -> add_atm (PRED (str, CONS(str))); positives := t; solve_pos ()
  | APP(head, arg1) -> 
    begin
      match (Norm.hnorm (APP(head, arg1))) with
      | CONS(str) -> add_atm (PRED (str, CONS(str))); positives := t; solve_pos ()
      | APP(CONS(str3), arg2) -> add_atm (PRED (str3, APP(CONS(str3), arg2))); 
          positives := t; solve_pos ()
    end
  
  | h -> print_term h; failwith " Solving not implemented for this case."

  (* Empty list, solve the atoms now *)

  (*| [] -> true*)
  with 
    | Failure "hd" -> true
    (*| Match_failure _ -> true*)


and solve_atm dummy = (*match !atoms with*)
try
let form = List.hd !atoms in
let t = List.tl !atoms in
match Term.observe form with
  | PRED (str, terms) -> (
    try match Hashtbl.find !clausesTbl str with
      | clauses -> (
        let rec attempt lst f = match lst with
          (*| LOLLI (s, f1, f2) :: t1 -> (
            try match unifies (LOLLI(s, f1, f2)) f with*)
          | lolli :: t1 -> (
            try match unifies lolli f with
              | (LOLLI(CONS(s), fp1, fp2), f_ptr) -> (
                let info = DATA(!goals, !positives, !atoms, (Hashtbl.copy !context), (Hashtbl.copy !clausesTbl)) in
                (*print_string "===== Context before trying to prove: "; print_term fp2; print_newline ();
                print_hashtbl !context; print_newline ();*)
                add_goals fp2;
                atoms := t;
                (match Hashtbl.find subexTpTbl s with
                  (*| LIN | AFF -> ( rmv_ctx (LOLLI(s, f1, f2)) s; rmv_cls (LOLLI (s, f1, f2)) )*)
                  | LIN | AFF -> ( rmv_ctx lolli s; rmv_cls lolli )
                  | REL | UNB -> () );
                if solve () then begin
                  solve_atm ()
                end
                else begin
                  (*(match Hashtbl.find subexTpTbl s with
                    (*| LIN | AFF -> ( add_ctx (LOLLI(s, f1, f2)) s; add_cls (LOLLI (s, f1, f2)) )*)
                    | LIN | AFF -> ( add_ctx lolli s; add_cls lolli )
                    | REL | UNB -> () );*)
                  reset info; (* FIXME: this should recover the formulas removed above. add_* should not have to be used.*)
                  attempt t1 f (* This is the backtracking on the lower level, during the backchaining. *)
                end
              )
              | (a, b) -> print_term a; print_string " and "; print_term b; print_newline ();
                failwith "Unexpected return from unifies"
              with 
                | Failure "Unification not possible." -> attempt t1 f
                | Failure "Head of a clause not a predicate." -> attempt t1 f
                | Failure "Formulas not compatible (should be lolli and pred)." -> attempt t1 f
                | Failure str -> failwith str
          )
          (*| _ :: t -> failwith "Not a lolli in clauses' table"*)
          | [] -> false
        in attempt clauses (PRED (str, terms))
      )
      with Not_found -> print_string "[ERROR] Atom not in table: "; print_string str; false
  )
  | bla -> failwith "\nNot an atom in atoms' list"
  (*| [] -> true*)
  with 
    | Failure "hd" -> true
    (*| Match_failure _ -> true*)


and backtrack dummy = (*print_string "\nBacktracking...\n" ;*)
  try match Stack.pop !states with
    | STATE (dt, f, POS, i) -> (
      reset dt; 
      try match List.nth !positives (i + 1) with
        | newf ->
          positives := make_first newf !positives;
          save_state newf POS (i + 1);
          solve_pos ()
        with Failure "nth" -> backtrack () (* Go back to the previous choice *) 
    )
    
    | STATE (dt, f, ATM, i) -> (
      reset dt;
      try match List.nth !atoms (i+1) with
        | newa -> 
          atoms := make_first newa !atoms;
          save_state newa ATM (i + 1);
          solve_atm ()
        with Failure "nth" -> backtrack ()
    )

    | STATE (dt, f, NEG, i) -> failwith "Negative formula on stack."

    with pop -> 
      print_string "\n[ERROR] Trying to backtrack with empty stack.\n";
      false
;;


