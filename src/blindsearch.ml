(*
 * Proof seach without backchaining.
 * No restriction on what kind of formula is in the context.
 * It is a bounded proof search.
 * One-sided sequent, inital rule: |- not A, A
 * Using only the goals list.
 * goals and context are global variables.
 * Not using the clauses table.
 *
 * Giselle Machado Reis - 2011
 *)

open Common
open Structs_macro
open Structs
open Term
open ProofTree
open Prints

(* Proves a LL formula *)

(* h is the maximum height of the proof. Set by the user or use 3 as default. *)
let rec prove h suc fail = prove_sync h suc fail

and prove_asyn h suc fail =
try
let form = List.hd !goals in
let t = List.tl !goals in
match Term.observe form with

  (* Assynchronous phase *)

  | LOLLI (sub, f1, f2) -> 
    if !verbose then begin
      print_endline "-- Lolli:"; 
      print_term (LOLLI(sub, f1, f2));
      print_newline ()
    end;
    add_ctx (deMorgan (NOT(f2))) (extract_str sub);
    goals := f1 :: t;
    let sq = SEQ(!context, !goals, ASYN) in
    activeseq := ProofTree.update !activeseq sq;
    prove_asyn h suc fail

  (* Solves f1 and f2 with the same context *)
  | WITH (f1, f2) -> begin
    if !verbose then begin
      print_endline "-- With 1st:"; 
      print_term (WITH(f1, f2));
      print_newline ()
    end;
    let orig_context = Hashtbl.copy !context in
    let orig_proof = ProofTree.copy !activeseq in
    goals := f1 :: t;
    (* Updates the proof tree for one in which the conclusion is f1 *)
    let sq = SEQ(!context, !goals, ASYN) in
    activeseq := ProofTree.update !activeseq sq;
    prove_asyn h (fun () -> 
      if !verbose then begin
        print_endline "-- With 2nd:"; 
        print_term (WITH(f1, f2));
        print_newline ()
      end;
      context := Hashtbl.copy orig_context;
      activeseq := ProofTree.copy orig_proof;
      goals := f2 :: t;
      let sq = SEQ(!context, !goals, ASYN) in
      activeseq := ProofTree.update !activeseq sq;
      prove_asyn h suc fail ()) fail
  end

  | PARR (f1, f2) -> 
    if !verbose then begin
      print_endline "-- Parr:"; 
      print_term (PARR(f1, f2));
      print_newline ()
    end;
    goals := f1 :: f2 :: t;
    let sq = SEQ(!context, !goals, ASYN) in
    activeseq := ProofTree.update !activeseq sq;
    prove_asyn h suc fail

  | QST (s, f) -> begin
    if !verbose then begin
      print_endline "-- Question mark:"; 
      print_term (QST(s, f));
      print_newline ()
    end;
    match Term.observe s with
      | CONS(sub) ->
        add_ctx f sub;
        goals := t;
        let sq = SEQ(!context, !goals, ASYN) in
        activeseq := ProofTree.update !activeseq sq;
        prove_asyn h suc fail
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
    prove_asyn h suc fail
  
  | TOP -> 
    if !verbose then begin
      print_endline "-- Top:"; 
      print_term TOP;
      print_newline ()
    end;
    is_top := true; 
    ProofTree.close !activeseq;
    (* TODO: create a data structure to accumulate formulas that can be weakened
     * because they appeared in a top. Update this here. Only the formulas from 
     * the context should be stored. *)
    suc

  | BOT -> 
    if !verbose then begin
      print_endline "-- Bottom:"; 
      print_term BOT;
      print_newline ()
    end;
    goals := t; 
    prove_asyn h suc fail

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
    prove_asyn h suc fail

  (* R arrow up rule *)
  (* Positive formulas and literals *)
  | ADDOR (_, _)
  | TENSOR (_, _)
  | EXISTS(_, _, _)
  | BANG (_, _)
  | HBANG (_, _)
  | ONE
  | COMP (_, _, _)
  | ASGN (_, _)
  | PRINT (_)
  | NOT(PRED(_, _, _))
  | PRED(_, _, _) ->
    if !verbose then begin
      print_endline "-- R arrow up:"; 
      print_term (Term.observe form);
      print_newline ()
    end;
    add_ctx form "$gamma";
    goals := t;
    prove_asyn h suc fail

  (* Negated formulas *)
  (* Apply deMorgan and try to prove them. *)
  | NOT(f) -> goals := (deMorgan (NOT(f))) :: t; prove_asyn h suc fail

  (* Things we are not yet solving *)
  | EQU (str, n, trm) -> print_string "Not solving term equality yet."; fail
  | CUT -> print_string "What should I do when encounter a cut?"; fail
  
  (* Why is this here????? *)
  (*| CONS(str) -> add_atm (PRED (str, CONS(str), NEG)); goals := t; solve_neg suc fail*)

  (* lambda terms *)
  | APP(head, arg1) -> 
    begin
      match (Norm.hnorm (APP( (Term.observe head), arg1))) with
      | f -> (match f with 
        | CONS(str) -> add_ctx (PRED (str, CONS(str), NEG)) "$gamma"; goals := t; prove_asyn h suc fail
        | APP(CONS(str3), arg2) -> 
          add_ctx (PRED (str3, APP(CONS(str3), arg2), NEG)) "$gamma"; 
          goals := t; prove_asyn h suc fail
	    | _ -> failwith "ERROR: line 330" (* this makes no sense... *)
      )
    end

(* We are not optimizing proof search here.
  | BRACKET(f) -> goals := t; add_goals (Term.observe f);
    let st = !nstates in 
    solve (fun () -> remove_states st; solve suc fail ()) fail
*)
  | BRACKET(f) -> print_string "Ignoring brackets during dumb proof search.";
    goals := f :: t;
    prove_asyn h suc fail

  | h -> print_term h; failwith " Solving not implemented for this case."

  (* Decide rules *)
  (* Empty list, apply one of the decide rules non-deterministically *)    
  with 
    | Failure "hd" -> 
      let ctx = to_pairs !context in
      decide h ctx suc fail


and prove_sync h suc fail =
try
let form = List.hd !goals in
(* OBS: this should be an empty list *)
let t = List.tl !goals in
match Term.observe form with

  (* R arrow down rule *)
  (* If a negative formulas was found, put it in goals list and go back to async phase *)     
  | LOLLI (sub, f1, f2) -> 
    begin 
    if !verbose then begin
      print_endline "-- R arrow down:"; 
      print_term (Term.observe form);
      print_newline ()
    end;
    match Term.observe sub with
      | CONS(s) -> 
        prove_asyn h suc fail
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
    prove_asyn h suc fail

  (* Synchronous phase *)

  | ADDOR (f1, f2) -> begin
    if !verbose then begin
      print_endline "-- O plus 1st:"; 
      print_term (Term.observe form);
      print_newline ()
    end;
    let orig_context = Hashtbl.copy !context in
    let orig_proof = ProofTree.copy !activeseq in
    goals := f1 :: t;
    (* Updates the proof tree for one in which the conclusion is f1 *)
    let sq = SEQ(!context, !goals, ASYN) in
    activeseq := ProofTree.update !activeseq sq;
    prove_sync h suc (fun () -> 
      if !verbose then begin
        print_endline "-- O plus 2st:"; 
        print_term (Term.observe form);
        print_newline ()
      end; 
      context := Hashtbl.copy orig_context;
      activeseq := ProofTree.copy orig_proof;
      goals := f2 :: t;
      ProofTree.setPremisses !activeseq [];
      let sq = SEQ(!context, !goals, ASYN) in
      activeseq := ProofTree.update !activeseq sq;
      prove_sync h suc fail ())
  end

  (* TODO: check this restore_atom st thing *)
  | TENSOR (f1, f2) ->
    if !verbose then begin
      print_endline "-- Tensor 1st:"; 
      print_term (Term.observe form);
      print_newline ()
    end; 
    let orig_proof = !activeseq in
    goals := f1 :: t;
    let sq = SEQ(!context, !goals, SYNC) in
    activeseq := ProofTree.update !activeseq sq;
    prove_sync h (fun () -> 
      if !verbose then begin
        print_endline "-- Tensor 2st:"; 
        print_term (Term.observe form);
        print_newline ()
      end; 
      goals := f2 :: t; 
      activeseq := orig_proof;
      let sq = SEQ(!context, !goals, SYNC) in
      activeseq := ProofTree.update !activeseq sq;
      (*let st = !nstates in *)
      prove_sync h suc fail ()) fail
      (*prove_sync h suc (fun () -> restore_atom st ()) ()) fail*)

  | EXISTS (s, i, f) ->
    if !verbose then begin
      print_endline "-- Exists:"; 
      print_term (Term.observe form);
      print_newline ()
    end;
    varid := !varid + 1;
    let new_var = VAR ({str = s; id = !varid; tag = Term.LOG; ts = 0; lts = 0}) in
    let newf = Norm.hnorm (APP (ABS (s, 1, f), [new_var])) in
    goals := newf :: t;
    let sq = SEQ(!context, !goals, ASYN) in
    activeseq := ProofTree.update !activeseq sq;
    prove_sync h suc fail
  
  | BANG (sub, f) -> 
    begin
      if !verbose then begin
        print_endline "-- Bang:"; 
        print_term (Term.observe form);
        print_newline ()
      end;
      match Term.observe sub with
      | CONS(s) -> 
        if condition_bang s then begin
          k_less_than s; 
          goals := f :: t;
          let sq = SEQ(!context, !goals, SYNC) in
          activeseq := ProofTree.update !activeseq sq;
          prove_asyn h suc fail
        end
        else fail
      | _ -> failwith "Not expected subexponential while solving positive formulas."
    end

  | HBANG (sub, f) -> begin
    if !verbose then begin
      print_endline "-- Hat bang:"; 
      print_term (Term.observe form);
      print_newline ()
    end;
    match Term.observe sub with
      | CONS (s) -> ( try match Hashtbl.find !context s with
        | [] -> 
          if !verbose then print_string ("Solved hbang "^s^".\n"); 
          goals := f :: t; 
          let sq = SEQ(!context, !goals, SYNC) in
          activeseq := ProofTree.update !activeseq sq;
          prove_asyn h suc fail 
        | _ -> 
          if !verbose then print_string ("Failed in hbang rule "^s^".\n"); 
          fail
        with Not_found -> 
          if !verbose then print_string ("Solved hbang "^s^".\n"); 
          goals := f :: t; 
          let sq = SEQ(!context, !goals, SYNC) in
          activeseq := ProofTree.update !activeseq sq;
          prove_asyn h suc fail
      )
      | _ -> failwith "Not expected subexponential while solving positive formulas."
    end

  (* TODO: I still need to check if gamma is empty or has formulas that
   * were in a top or has formulas that can be splitted to the other side. *)
  | ONE -> 
    if !verbose then begin
      print_endline "-- ONE:"; 
      print_term (Term.observe form);
      print_newline ()
    end;
    goals := t; 
    ProofTree.close !activeseq;
    suc 

  | COMP (ct, t1, t2) -> 
    if (solve_cmp ct t1 t2) then begin
      goals := t;
      if (List.length !positives) != 0 then
        save_state (COMP(ct, t1, t2)) !bind_len suc fail [] SYNC;
        prove_sync h suc fail
    end   
    else fail

  | ASGN (t1, t2) -> 
    if (solve_asgn t1 t2) then begin
      goals := t;
      if (List.length !positives) != 0 then
        save_state (ASGN (t1, t2)) !bind_len suc fail [] SYNC;
      prove_sync h suc fail
    end    
    else fail

  | PRINT (t1) -> print_endline ""; print_term t1; print_endline "";
     goals := t;
     if (List.length !positives) != 0 then
       save_state (PRINT (t1)) !bind_len suc fail [] SYNC;
       prove_sync h suc fail

  (* Initial rules *)
  | PRED (str, terms, p) ->
    if !verbose then begin
      print_endline "-- Initial:"; 
      print_term (Term.observe form);
      print_newline ();
      print_endline "State of the context: ";
      print_hashtbl !context;
    end; 
    if condition_init (NOT(PRED(str, terms, p))) then suc
    else fail
  | NOT(PRED (str, terms, p)) ->
    if !verbose then begin
      print_endline "-- Initial:"; 
      print_term (Term.observe form);
      print_newline ();
      print_endline "State of the context: ";
      print_hashtbl !context;
    end;
    if condition_init (PRED(str, terms, p)) then suc
    else fail

  (* Things we are not solving *)
  | EQU (str, n, trm) -> print_string "Not solving term equality yet."; fail
  | CUT -> print_string "What should I do when encounter a cut?"; fail

  (* Why is this here? *)
(*  | CONS(str) -> add_atm (PRED (str, CONS(str), NEG)); positives := t; solve_pos suc fail*)

  (* lambda terms *)
  | APP(head, arg1) -> 
    begin
      match (Norm.hnorm (APP(head, arg1))) with
      | CONS(str) -> 
        goals := (PRED (str, CONS(str), NEG)) :: t; 
        prove_sync h suc fail
      | APP(CONS(str3), arg2) -> 
        goals := (PRED (str3, APP(CONS(str3), arg2), NEG)) :: t; 
        prove_sync h suc fail
      | _ -> failwith "Error while normalizing lambda term."
    end
  
  | h -> print_term h; failwith " Solving not implemented for this case."

  (* Empty list in synchronous phase: fail *)
  with 
    | Failure "hd" -> failwith "Something went terribly wrong."


(* ctx is the context in the form of a list of pairs. *)
and decide h ctx suc fail = 
  if h <= 0 then begin
    if !verbose then print_endline "Failed because it's bounded.";
    fail
  end
  else begin
    match ctx with
      | [] -> fail (* No more formulas available to pick from the context. *)
      | (s, form) :: tl ->
        let orig_context = Hashtbl.copy !context in
        (*print_endline "Context saved:";
        print_hashtbl !context;*)
        (* Remove the formula from the context, if this is the case. *)
        (match type_of s with
          | LIN | AFF -> rmv_ctx form s;
          | REL | UNB ->  () 
        );
        (* Focus on the formula *)
        goals := (Term.observe (apply_ptr form))::[];
        if !verbose then begin
          print_endline "-- Decide:";
          print_int h; print_newline();
          print_term (List.hd !goals);
          print_newline ()
        end;
        let sq = SEQ(!context, !goals, ASYN) in
        activeseq := ProofTree.update !activeseq sq;
        let h1 = h - 1 in
        prove_sync h1 suc 
          (fun () -> 
            (*(match type_of s with
              | LIN | AFF -> add_ctx form s;
              | REL | UNB ->  () 
            );*)
            (* XXX: Should I restore the contexts? yep *)
            context := Hashtbl.copy orig_context;
            (*print_endline "Context recovered:";
            print_hashtbl !context;*)
            if !verbose then begin
              print_endline "Failed, deciding again...";
              print_endline "Available options: ";
              List.iter (fun (s, f) -> print_term f; print_string " || ";) tl;
              print_newline ()
            end;
            decide h tl suc fail ())
  end
;;

