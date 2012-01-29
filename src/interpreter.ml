open Common
open Structs_macro
open Structs
open Term
open ProofTree
open Prints

(* Solves a LL formula *)

(* Classic version *)
(* TODO: I should start with a positive phase... review this. *)
let rec solve suc fail = solve_neg suc fail

and solve_neg suc fail =
try
let form = List.hd !goals in
let t = List.tl !goals in
match Term.observe form with

  (* Negative formulas *)

  (* Put f1 in subexponential s of the context, put (f1, s) in head f1 of clausesTbl and continue with f2 *)
  (* If s is $gamma (linear implication), decompose f1 up to negatives and atoms and put these formulas in $gamma *)
  (* Otherwise, put f1 in subexponential s and f1 :- f2 in the clauses hash 
  (Note that f1 is either an atom or -o if it's in a subexponential.) *)
  | LOLLI (sub, f1, f2) -> (
    if !verbose then begin
      print_endline "-- Lolli:"; 
      print_term (LOLLI(sub, f1, f2));
      print_newline ()
    end;
    match (Term.observe sub) with
    | CONS("$gamma") -> 
      let terminate = ref true in
      let rec decompose f = match f with
        | TENSOR (form1, form2) -> decompose form1; decompose form2
        | BANG (s, form) | HBANG (s, form) -> ( match form, (Term.observe s) with
          | PRED(str,terms, p), CONS(sub) -> 
            add_ctx (LOLLI (CONS(sub), PRED(str,terms,p), ONE)) sub;
            add_cls (LOLLI (CONS(sub), PRED(str,terms,p), ONE))
          | LOLLI(CONS(se), fl1, fl2), CONS(sub) ->
            add_ctx (LOLLI(CONS(se), fl1, fl2)) se;
            add_cls (LOLLI(CONS(se), fl1, fl2))
          | _ -> failwith "Lolli head error or unitialized subexponential"
        )
        | PRED (str, terms, p) ->
          add_lin (LOLLI (CONS("$gamma"), PRED(str,terms,p), ONE));
          add_cls (LOLLI (CONS("$gamma"), PRED(str,terms,p), ONE))
        | COMP(ct, t1, t2) -> if solve_cmp ct t1 t2 then () 
          else terminate := true
        | ASGN( t1, t2) -> if solve_asgn t1 t2 then () 
          else terminate := true
        | PRINT(t1) -> print_endline ""; print_term t1; print_endline ""
        | x -> add_lin x (* Negative formula or atom *)
      in decompose f2; 
      goals := (f1 :: t);
      let sq = SEQ(!context, !goals, ASYN) in
      activeseq := ProofTree.update !activeseq sq;
      if !terminate then suc else solve_neg suc fail
    | CONS(subexp) -> ( match f2 with
      (* TODO: Should I check the cases for equalities here also? What about the rest of the cases? *)
      | PRED(str,terms,p) ->
        add_ctx (LOLLI (CONS(subexp), PRED(str,terms,p), ONE)) subexp;
        add_cls (LOLLI (CONS(subexp), PRED(str,terms,p), ONE));
        goals := (f1 :: t);
        let sq = SEQ(!context, !goals, ASYN) in
        activeseq := ProofTree.update !activeseq sq;
        solve_neg suc fail
      | LOLLI(sub2, fl1, fl2) ->
        begin match sub2 with
          | CONS(se) ->
            add_ctx (LOLLI(CONS(se), fl1, fl2)) se;
            add_cls (LOLLI(CONS(se), fl1, fl2)); 
            goals := (f1 :: t);
            let sq = SEQ(!context, !goals, ASYN) in
            activeseq := ProofTree.update !activeseq sq;
            solve_neg suc fail
          | _ -> failwith "Unitialized subexponential while solving negative formulas."
        end
      | _ -> failwith "Lolli head error"
    )
    | _ -> failwith "Subexponential error in lolli."
  )

  (* Solves f1 and f2 with the same context *)
  | WITH (f1, f2) -> begin
    if !verbose then begin
      print_endline "-- With 1st:"; 
      print_term (WITH(f1, f2));
      print_newline ()
    end;
    let orig_context = !context in
    let orig_states = !states in
    let orig_clauses = !clausesTbl in
    let orig_proof = !activeseq in
    goals := f1 :: t;
    (* Updates the proof tree for one in which the conclusion is f1 *)
    let sq = SEQ(!context, !goals, ASYN) in
    activeseq := ProofTree.update !activeseq sq;
    solve_neg (fun () -> 
      if !verbose then begin
        print_endline "-- With 2st:"; 
        print_term (WITH(f1, f2));
        print_newline ()
      end;
      context := orig_context;
      states := orig_states;
      clausesTbl := orig_clauses;
      activeseq := orig_proof;
      goals := f2 :: t;
      let sq = SEQ(!context, !goals, ASYN) in
      activeseq := ProofTree.update !activeseq sq;
      solve_neg suc fail ()) fail
  end

  | PARR (f1, f2) -> 
    if !verbose then begin
      print_endline "-- Parr:"; 
      print_term (PARR(f1, f2));
      print_newline ()
    end;
    let tl = f2 :: t in
    goals := f1 :: tl;
    let sq = SEQ(!context, !goals, ASYN) in
    activeseq := ProofTree.update !activeseq sq;
    solve_neg suc fail

  (* TODO: modify this to decompose the formula just like it's done in LOLLI *)
  | QST (s, f) -> begin
    if !verbose then begin
      print_endline "-- Question mark:"; 
      print_term (QST(s, f));
      print_newline ()
    end;
    match Term.observe s with
    | CONS(sub) ->
      add_ctx (LOLLI (CONS(sub), f, ONE)) sub;
      add_cls (LOLLI (CONS(sub), f, ONE));
      goals := t;
      let sq = SEQ(!context, !goals, ASYN) in
      activeseq := ProofTree.update !activeseq sq;
      solve_neg suc fail
    | _ -> failwith "Not an exponential in question mark."
  end

  | FORALL (s, i, f) ->
    if !verbose then begin
      print_endline "-- Forall:"; 
      print_term (FORALL(s, i, f));
      print_newline ()
    end;
    varid := !varid + 1;
    let new_var = VAR ({str = s; id = !varid; tag = Term.EIG; ts = 0; lts = 0}) in
    let newf = Norm.hnorm (APP (ABS (s, 1, f), [new_var])) in
    goals := newf :: t;
    let sq = SEQ(!context, !goals, ASYN) in
    activeseq := ProofTree.update !activeseq sq;
    solve_neg suc fail
  
  | TOP -> 
    if !verbose then begin
      print_endline "-- Top:"; 
      print_term (TOP);
      print_newline ()
    end;
    is_top := true; 
    ProofTree.close !activeseq;
    suc (* TODO: This is in fact not correct. We have to mark the formulas in the context that can be weakened. *)

  | BOT -> 
    if !verbose then begin
      print_endline "-- Bottom:"; 
      print_term (BOT);
      print_newline ()
    end;
    goals := t; 
    solve_neg suc fail

  | NEW (s, t1) -> 
    if !verbose then begin
      print_endline "-- New subexponential:"; 
      print_term (NEW(s, t1));
      print_newline ()
    end;
    varid := !varid + 1;
    let string_sub = "NSUBEXP"^(string_of_int !varid) in
    let new_cons = CONS string_sub in
    let newf = Norm.hnorm (APP (ABS (s, 1, t1), [new_cons])) in
    new_subexp string_sub;
    goals := newf :: t;
    let sq = SEQ(!context, !goals, ASYN) in
    activeseq := ProofTree.update !activeseq sq;
    solve_neg suc fail

  (* Positive formulas *)

  | ADDOR (_, _) 
  | TENSOR (_, _) 
  | EXISTS(_, _, _) 
  | BANG (_, _) 
  | HBANG (_, _) 
  | ONE 
  | COMP (_, _, _) 
  | ASGN (_, _) 
  | PRINT (_) -> 
    if !verbose then begin
      print_endline "-- R arrow up:"; 
      print_term (Term.observe form);
      print_newline ()
    end;
    add_pos form;
    goals := t;
    solve_neg suc fail

  (* Atoms *)
  | PRED(str, terms, p) -> 
    if !verbose then begin
      print_endline "-- R arrow up:"; 
      print_term (Term.observe form);
      print_newline ()
    end;
    add_atm (PRED(str, terms, p)); 
    goals := t; 
    solve_neg suc fail

  | EQU (str, n, trm) -> print_string "Not solving term equality yet."; fail
  | CUT -> print_string "What should I do when encounter a cut?"; fail
  | CONS(str) -> add_atm (PRED (str, CONS(str), NEG)); goals := t; solve_neg suc fail
  | APP(head, arg1) -> 
    begin
      match (Norm.hnorm (APP( (Term.observe head), arg1))) with
      | f -> (match f with 
        | CONS(str) -> add_atm (PRED (str, CONS(str), NEG)); goals := t; solve_neg suc fail
        | APP(CONS(str3), arg2) -> 
          add_atm (PRED (str3, APP(CONS(str3), arg2), NEG)); 
          goals := t; solve_neg suc fail
	    | _ -> failwith "ERROR: line 330" (* print_string "Line 330 - interpreter.ml: "; print_term f; print_newline (); flush stdout *)
      )
    end

  | BRACKET(f) -> goals := t; add_goals (Term.observe f);
    let st = !nstates in 
    solve (fun () -> remove_states st; solve suc fail ()) fail

  | h -> print_term h; failwith " Solving not implemented for this case."

  (* Empty list, solve the positive formulas now *)    
  with 
    | Failure "hd" -> solve_pos suc fail


and solve_pos suc fail =
try
let form = List.hd !positives in
let t = List.tl !positives in
match Term.observe form with

  (* If a negative formulas was found, put it in goals list and call solve again (back to async phase) *)
     
  | LOLLI (sub, f1, f2) -> 
    if !verbose then begin
      print_endline "-- R arrow down:"; 
      print_term (Term.observe form);
      print_newline ()
    end;
    begin 
      match Term.observe sub with
      | CONS(s) -> 
        add_goals (LOLLI (sub, f1, f2)); 
        solve_neg (fun () -> solve_pos suc fail ()) fail (* G: I think I can replace this with 'solve suc fail' *)
      | _ -> failwith "Unitialized subexponential while solving postive formulas."
    end

  | WITH (_, _) 
  | PARR (_, _) 
  | QST (_, _) 
  | FORALL (_, _, _) 
  | TOP 
  | BOT 
  | NEW (_, _) -> 
    if !verbose then begin
      print_endline "-- R arrow down:"; 
      print_term (Term.observe form);
      print_newline ()
    end;
    add_goals form;
    solve_neg (fun () -> solve_pos suc fail ()) fail
    
  (* Positive formulas *)

  | ADDOR (f1, f2) -> begin
    if !verbose then begin
      print_endline "-- O plus 1st:"; 
      print_term (ADDOR(f1, f2));
      print_newline ()
    end;
    let orig_context = !context in
    let orig_states = !states in
    let orig_clauses = !clausesTbl in
    let orig_proof = !activeseq in
    let orig_goals = !goals in
    (*add_goals f1;*)
    positives := f1 :: t;
    (* Updates the proof tree for one in which the conclusion is f1 *)
    let sq = SEQ(!context, !positives, ASYN) in
    activeseq := ProofTree.update !activeseq sq;
    solve_pos suc (fun () -> 
      if !verbose then begin
        print_endline "-- O plus 2st:"; 
        print_term (ADDOR(f1, f2));
        print_newline ()
      end;
      context := orig_context;
      states := orig_states;
      clausesTbl := orig_clauses;
      activeseq := orig_proof;
      goals := orig_goals;
      (*add_goals f2;*)
      positives := f2 :: t;
      ProofTree.setPremisses !activeseq [];
      let sq = SEQ(!context, !positives, ASYN) in
      activeseq := ProofTree.update !activeseq sq;
      solve_pos suc fail ())
  end

  | TENSOR (f1, f2) ->
    if !verbose then begin
      print_endline "-- Tensor 1st:"; 
      print_term (TENSOR(f1, f2));
      print_newline ()
    end;
    let orig_proof = !activeseq in
    (*add_goals f1;*)
    positives := f1 :: t;
    let sq = SEQ(!context, !positives, SYNC) in
    activeseq := ProofTree.update !activeseq sq;
    (*positives := t;*)
    solve_pos (fun () -> (*add_goals f2; *)
      if !verbose then begin
        print_endline "-- Tensor 2st:"; 
        print_term (TENSOR(f1, f2));
        print_newline ()
      end;
      positives := f2 :: t;
      activeseq := orig_proof;
      let sq = SEQ(!context, !positives, SYNC) in
      activeseq := ProofTree.update !activeseq sq;
      let st = !nstates in 
      solve_pos suc (fun () -> restore_atom st ()) ()) fail

  | EXISTS (s, i, f) ->
    if !verbose then begin
      print_endline "-- Exists:"; 
      print_term (EXISTS(s, i, f));
      print_newline ()
    end;
    varid := !varid + 1;
    let new_var = VAR ({str = s; id = !varid; tag = Term.LOG; ts = 0; lts = 0}) in
    let newf = Norm.hnorm (APP (ABS (s, 1, f), [new_var])) in
    positives := newf :: t;
    let sq = SEQ(!context, !positives, ASYN) in
    activeseq := ProofTree.update !activeseq sq;
    solve_pos suc fail
  
  | BANG (sub, f) -> 
    begin
      if !verbose then begin
        print_endline "-- Bang:"; 
        print_term (BANG(sub, f));
        print_newline ()
      end;
      match Term.observe sub with
      | CONS(s) -> 
        if condition_bang s then begin
          k_less_than s; 
          positives := t;
          add_goals f;
          let sq = SEQ(!context, !goals, ASYN) in
          activeseq := ProofTree.update !activeseq sq;
          solve_neg suc fail
          (* I will not save the state here. If f is proved, I would have to make
             positives := []; save_state ...; solve_pos ()
             which would yield true anyway
          *)
        end
        else fail
      | _ -> failwith "Not expected subexponential while solving positive formulas."
    end

  | HBANG (sub, f) -> begin
    if !verbose then begin
      print_endline "-- Hat bang:"; 
      print_term (HBANG(sub, f));
      print_newline ()
    end;
    match Term.observe sub with
      | CONS (s) -> ( try match Hashtbl.find !context s with
        | [] -> 
          if !verbose then print_string ("Solved hbang "^s^".\n"); 
          positives := t; 
          add_goals f; 
          let sq = SEQ(!context, !goals, ASYN) in
          activeseq := ProofTree.update !activeseq sq;
          solve_neg suc fail 
        | _ -> 
          if !verbose then print_string ("Failed in hbang rule "^s^".\n"); 
          fail
        with Not_found -> 
          if !verbose then print_string ("Solved hbang "^s^".\n"); 
          positives := t; 
          add_goals f; 
          let sq = SEQ(!context, !goals, ASYN) in
          activeseq := ProofTree.update !activeseq sq;
          solve_neg suc fail
      )
      | _ -> failwith "Not expected subexponential while solving positive formulas."
    end

  | ONE -> 
    if !verbose then begin
      print_endline "-- One:"; 
      print_term (ONE);
      print_newline ()
    end;
    positives := t; 
    ProofTree.close !activeseq;
    suc 
    (* If I am solving a tensor, I can leave the checking of empty context for the next formula. *)
    (*if empty_nw () then begin
      positives := t;
      if (List.length !positives) != 0 then
        save_state (List.hd !positives) POS 0 suc fail;
      solve_pos suc fail
    end    
    else fail ()*)

  (* G: I think we don't have to save states in these cases... Why would we? Maybe if we were dealing with classical logic. *)

  | COMP (ct, t1, t2) -> 
    if (solve_cmp ct t1 t2) then begin
      positives := t;
      if (List.length !positives) != 0 then
        save_state (COMP(ct, t1, t2)) !bind_len suc fail [] SYNC;
        solve_pos suc fail
    end    
    else fail

  | ASGN (t1, t2) -> 
    if (solve_asgn t1 t2) then begin
      positives := t;
      if (List.length !positives) != 0 then
        save_state (ASGN (t1, t2)) !bind_len suc fail [] SYNC;
      solve_pos suc fail
    end    
    else fail

  | PRINT (t1) -> print_endline ""; print_term t1; print_endline "";
     positives := t;
     if (List.length !positives) != 0 then
       save_state (PRINT (t1)) !bind_len suc fail [] SYNC;
     solve_pos suc fail

  (* Atoms *)
  | PRED (str, terms, p) -> add_atm (PRED (str, terms, p)); positives := t; solve_pos suc fail

  | EQU (str, n, trm) -> print_string "Not solving term equality yet."; fail
  | CUT -> print_string "What should I do when encounter a cut?"; fail
  | CONS(str) -> add_atm (PRED (str, CONS(str), NEG)); positives := t; solve_pos suc fail
  | APP(head, arg1) -> 
    begin
      match (Norm.hnorm (APP(head, arg1))) with
      | CONS(str) -> add_atm (PRED (str, CONS(str), NEG)); positives := t; solve_pos suc fail
      | APP(CONS(str3), arg2) -> add_atm (PRED (str3, APP(CONS(str3), arg2), NEG)); 
          positives := t; solve_pos suc fail
      | _ -> failwith "Not expected term when solving application."
    end
  
  | h -> print_term h; failwith " Solving not implemented for this case."

  (* Empty list, solve the atoms now *)
  with 
    | Failure "hd" -> solve_atm suc fail


and solve_atm_aux suc fail forms =
let form = List.hd !atoms in
let t = List.tl !atoms in
match Term.observe form with
  | PRED (str, terms, p) -> (
    try match forms with
      | lolli :: t1 -> (
        try match unifies lolli (PRED(str, terms, p)) with
          | (LOLLI(CONS(s), fp1, fp2), f_ptr) -> (
	    (* G: Where is a new entry in the stack created here?? *)
            if !verbose then print_endline "Creating a new entry in the stack without deleting.";
            (match type_of s with
              | LIN | AFF -> ( rmv_ctx lolli s; rmv_cls lolli )
              | REL | UNB ->  () 
            );
            atoms := t;
            add_goals fp2;
            let sq = SEQ(!context, !goals, ASYN) in
            activeseq := ProofTree.update !activeseq sq;
            solve suc fail
          )
          | (a, b) -> print_term a; print_string " and "; print_term b; print_newline ();
            failwith "Unexpected return from unifies"
          with 
            | Failure "Unification not possible." -> if !verbose then print_string "Unification failure.\n"; fail
	    (* G: I think these two next failures should be treated as a program failure, not the proof. *)
            (*| Failure "Head of a clause not a predicate." -> fail ()
            | Failure "Formulas not compatible (should be lolli and pred)." -> fail ()*)
            | Failure str -> failwith str
          )
      | [] -> 
        if !verbose then begin
          print_string ("No clauses for this atom: "^str^".\n"); 
          print_string "Backtracking...\n"
        end;
        fail
      with Not_found -> 
        if !verbose then begin
          print_string "[ERROR] Atom not in table: "; 
	      print_string str
	    end;
	    fail
  )
  | bla -> failwith "\nNot an atom in atoms' list"


and solve_atm suc fail = (*trying to prove an atom and needing to initialize the stack*)
try
let form = List.hd !atoms in
let t = List.tl !atoms in
match Term.observe form with
  | PRED (str, terms, p) -> 
    (*If tabling is activated, then check whether current context has already shown to be a failure*)
    if (not !tabling) || ( !tabling && not_in_fail_table (PRED (str, terms, p)) ) then 
      begin
        if !verbose then
          begin
            print_endline "Did not find the current state in the fail table: ";
            print_term (PRED (str, terms, p)); print_string "\n";
          end;
        try 
        begin
          match Hashtbl.find !clausesTbl str with
          | lolli :: t1 -> 
            let bind_b4 = !bind_len in (*We need to get the binding of substitutions used until this point, not after the next unification.*)
            atoms := form :: t;
            save_state (PRED(str, terms, p)) bind_b4 suc fail t1 ASYN;
            let st = !nstates in
            let orig_proof = !activeseq in
            solve_atm_aux suc (fun () -> activeseq := orig_proof;
              ProofTree.setPremisses !activeseq []; restore_atom st ()) (lolli :: t1)
          | [] -> begin 
            if !verbose then begin
              print_string ("No clauses for this atom: "^str^".\n"); 
              print_string "Backtracking...\n"
            end;
            fail
          end
        end
        with Not_found -> 
          if !verbose then begin
            print_string "[ERROR] Atom not in table: "; 
          print_string str
        end;
        fail
      end
    (*It has been already shown that this predicate is not provable using the current context.*)
    else begin 
      if !verbose then print_endline "Tabling at work!\n"; 
      fail
    end
  | bla -> failwith "\nNot an atom in atoms' list"
  with 
    | Failure "hd" -> suc

and back_chain forms suc fail = (*already initialized the stack, but now we need to backtrack using another clause in the context.*)
try
let form = List.hd !atoms in
let t = List.tl !atoms in
match Term.observe form with
  | PRED (str, terms, p) -> begin
    try 
      begin
        match forms with
        | lolli :: t1 -> 
          let bind_b4 = !bind_len in
          atoms := form :: t;
          (*Removing the top of the stack, so that a new one is pushed 
           with a smaller list of formulas to backtrack on.*)
          let _ = Stack.pop !states in
	        nstates := !nstates - 1; 
          save_state (PRED(str, terms, p)) bind_b4 suc fail t1 ASYN;
          let st = !nstates in
          let orig_proof = !activeseq in
          solve_atm_aux suc (fun () -> activeseq := orig_proof;
            ProofTree.setPremisses !activeseq []; restore_atom st ()) forms
        | [] -> 
	      if !verbose then begin
	        print_string ("No clauses for this atom: "^str^".\n"); 
	        print_string "Backtracking...\n"
	      end; 
          (*It has been shown that this goal is not provable using the current context. Hence add it 
          to the fail table.*)
          if !tabling then begin
            if !verbose then print_string "Adding state to fail_table...\n";
            Hashtbl.add !fail_table (PRED (str, terms, p)) !context
          end;
	      fail
      end
      with Not_found -> 
        if !verbose then begin
          print_string "[ERROR] Atom not in table: "; 
	      print_string str
        end;
        fail
  end
  | bla -> failwith "\nNot an atom in atoms' list"
  with 
    | Failure "hd" -> suc

and restore_atom n = let s = Stack.length !states in
  if !verbose then begin
    print_string "Restoring states: "; 
    print_int n; print_newline ()
  end;
  assert (n <= s);
  for i = 1 to s-n do
    let STATE(_, _, _, _, _, _, _) = Stack.pop !states in
      nstates := !nstates - 1
  done;
  let STATE(dt, _, bl, sc, fl, bck, _) = Stack.top !states in
  reset dt;
  restore_state bl;
  back_chain bck sc fl
;;
