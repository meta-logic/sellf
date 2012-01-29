open Term
open Prints
open Structs
open Structs_macro
open ProofTree
open Constraints
open Common

let getGoals seq = match seq with
  | SEQM(_, g, _) -> g
  | EMPSEQ -> failwith "Previous sequent is the empty one."
  | SEQ(_, _, _) -> failwith "Using wrong type of sequent for macro rules."
;;

(* Generates the constraints for the initial rule *)
let initCstrsAux ctx form s i = 
  let isHere = match type_of s with
    | UNB | AFF -> Constraints.MCTX(form, (s, i))
    | LIN | REL -> Constraints.ELIN(form, (s, i))
  in
  let rec restIsEmpty x ctx = 
  Hashtbl.fold (fun s i acc ->
    if x != s then begin
      match type_of s with
        | UNB | AFF -> acc (* No constraints. *)
        | LIN | REL -> Constraints.EMP(s, i) :: acc
    end else acc
    ) ctx []
  in isHere :: (restIsEmpty s ctx)

let rec genInitCstrs ctx form = Hashtbl.fold (fun s i lst -> (initCstrsAux ctx form s i) :: lst) ctx []

(* Generates macro rules for a LL term on the right side *)

(* TODO: Check if there is only one formula in forms when necessary.  *)
let rec rmacro suc =
try
let forms = getGoals (ProofTree.getConclusion !currentroot) in
let form = List.hd forms in
match Term.observe form with

(* Negative formulas *)

  (* RULE: & *)
  (* Solves f1 and f2 with the same context *)
  | WITH (f1, f2) -> begin
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let seq = SEQM(prevctx, f1 :: (List.tl forms), ASYN) in
    let orig_tree = !currentroot in
    currentroot := ProofTree.update !currentroot seq;  
    rmacro (fun () -> 
      currentroot := orig_tree;
      let seq2 = SEQM(prevctx, f2 :: (List.tl forms), ASYN) in
      currentroot := ProofTree.update !currentroot seq2;
      rmacro suc)
  end

  (* RULE: inverted with *)
  | PARR (f1, f2) ->
    let ctx0 = getContexts (ProofTree.getConclusion !currentroot) in
    let seq = SEQM(ctx0, f1 :: f2 :: (List.tl forms), SYNC) in
    currentroot := ProofTree.update !currentroot seq;
    rmacro suc


  | FORALL (s, i, f) ->
      varid := !varid + 1;
      let new_var = VAR ({str = s; id = !varid; tag = Term.EIG; ts = 0; lts = 0}) in
      let newf = Norm.hnorm (APP (ABS (s, 1, f), [new_var])) in
      let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
      let seq = SEQM(prevctx, newf :: (List.tl forms), ASYN) in
      currentroot := ProofTree.update !currentroot seq;
      rmacro suc
 
  (* RULE: T *)
  | TOP -> is_top := true; 
    (*let seq = ProofTree.getConclusion !currentroot in*)
    (*leaves := seq :: !leaves;*)
    ProofTree.close !currentroot;
    suc () (* This is in fact not correct. We have to mark the formulas in the context that can be weakened. *)

  (* RULE: bottom *)
  | BOT ->
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let seq = SEQM(prevctx, (List.tl forms), ASYN) in
    currentroot := ProofTree.update !currentroot seq;
    rmacro suc

  (* RULE: ?*)
  | QST(sub, t) -> begin
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let newctx = Hashtbl.copy prevctx in
    match Term.observe sub with
      | CONS(s) -> begin 
        let i = Hashtbl.find !macroctx s in
        let ilcl = Hashtbl.find prevctx s in
        (match type_of s with
          | LIN | AFF -> 
            (* Updating global counter *)
            Hashtbl.remove !macroctx s;
            Hashtbl.add !macroctx s (i+2);
            (* Updating the new context *)
            Hashtbl.remove newctx s;
            Hashtbl.add newctx s (i+2);
            (* Adding the constraints *)
            Constraints.add !constrs [[
              Constraints.ELIN(t, (s, (i+1)));
              Constraints.UNION((s, ilcl), (s, (i+1)), (s, (i+2)))
            ]]
          | UNB | REL -> 
            (* Updating global counter *)
            Hashtbl.remove !macroctx s;
            Hashtbl.add !macroctx s (i+1);
            (* Updating the new context *)
            Hashtbl.remove newctx s;
            Hashtbl.add newctx s (i+1);
            (* Adding the constraints *)
            Constraints.add !constrs [[
              Constraints.ADDFORM(t, (s, ilcl), (s, (i+1)))
            ]]
        );
        let seq = SEQM(newctx, (List.tl forms), ASYN) in
        currentroot := ProofTree.update !currentroot seq;
        rmacro suc
        end
      | _ -> failwith "Not expected subexponential while solving [l]?."
  end

  | NEW (s, t1) -> 
    varid := !varid + 1;
    let string_sub = "NSUBEXP"^(string_of_int !varid) in
    let new_cons = CONS string_sub in
    let newf = Norm.hnorm (APP (ABS (s, 1, t1), [new_cons])) in
    new_subexp string_sub;
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let seq = SEQM(prevctx, newf :: (List.tl forms), ASYN) in
    currentroot := ProofTree.update !currentroot seq;  
    rmacro suc

  (* Positive formulas *)

  (* RULE: + *)
  | ADDOR (f1, f2) ->
    let mirror = ProofTree.copy !macrorule in
    (*let leaves = ProofTree.getOpenLeaves !macrorule in*)
    let orig_cstr = Constraints.copy !constrs in
    let orig_root = !currentroot in
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let seq = SEQM(prevctx, f1 :: (List.tl forms), ASYN) in
    currentroot := ProofTree.update !currentroot seq;  
    (*let p = !leaves in*)
    rmacro (fun () -> 
        suc (); (* This is supposed to save the previous macro rule *)
        (*macrorule := mcr_so_far;*)
        (*List.iter (fun l -> ProofTree.setPremisses l []) leaves;*)
        (*currentroot := ProofTree.getLatestPremisse !macrorule;*)
        ProofTree.mask mirror !macrorule;
        currentroot := orig_root;
        (*ProofTree.setPremisses !currentroot [];*)
        constrs := orig_cstr;
        let seq2 = SEQM(prevctx, f2 :: (List.tl forms), ASYN) in
        currentroot := ProofTree.update !currentroot seq2;  
        (*leaves := p;*)
        rmacro suc
        )

  (* RULE: x *)
  | TENSOR (f1, f2) ->
    (* Get the previous context to know what is the number that's the union *)
    (* Get current global counter to find out the new numbers *)
    let ctx0 = getContexts (ProofTree.getConclusion !currentroot) in
    let ctx1 = Hashtbl.copy ctx0 in
    let ctx2 = Hashtbl.copy ctx0 in
    let rec splitLinear lst = match lst with
      | [] -> ()
      | s::t -> match type_of s with
        | LIN | REL -> 
          let i = Hashtbl.find !macroctx s in
          let prev = Hashtbl.find ctx0 s in
          (* Updating global counter of s *)
          Hashtbl.remove !macroctx s;
          Hashtbl.add !macroctx s (i+2);
          (* Creating new s context for each branch *)
          Hashtbl.remove ctx1 s;
          Hashtbl.add ctx1 s (i+1);
          Hashtbl.remove ctx2 s;
          Hashtbl.add ctx2 s (i+2);
          (* Creating the union constraints *)
          Constraints.add !constrs [[
            Constraints.UNION((s, i+1), (s, i+2), (s, prev))
            ]];
          splitLinear t
        | UNB | AFF -> splitLinear t
    in splitLinear (keys !macroctx);

    let orig_root = !currentroot in
    let seq = SEQM(ctx1, f1 :: (List.tl forms), SYNC) in
    currentroot := ProofTree.update !currentroot seq;
    rmacro (fun () -> 
      let seq2 = SEQM(ctx2, f2 :: (List.tl forms), SYNC) in
      currentroot := orig_root;
      currentroot := ProofTree.update !currentroot seq2;
      rmacro suc)

  (* RULE: ! *)
  | BANG (sub, f) -> 
    begin
      match Term.observe sub with
      | CONS(s) -> begin
        let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
        let ctx1 = Hashtbl.copy prevctx in
        
        let rec applyBang s idxs = match idxs with
          | [] -> ()
          | i::t -> 
            match type_of i with 
            (* This can suffer weakening, erase the formulas when necessary *)
              | UNB | AFF ->  begin
                if i = s || (greater_than i s) then applyBang s t
                else begin
                  let idx = Hashtbl.find !macroctx i in
                  Hashtbl.remove ctx1 i;
                  Hashtbl.add ctx1 i (idx+1);
                  Hashtbl.remove !macroctx i;
                  Hashtbl.add !macroctx i (idx+1);
                  (* TODO: this can be optimized if we gather all constraints at
                  first in a list and add them afterwards. *)
                  Constraints.add !constrs [[(Constraints.EMP(i, idx+1))]];
                end
              end
              | REL | LIN -> begin
                if i = s || (greater_than i s) then applyBang s t
                else begin
                  let idx = Hashtbl.find ctx1 i in
                  (* TODO: this can be optimized if we gather all constraints at
                  first in a list and add them afterwards. *)
                  Constraints.add !constrs [[(Constraints.EMP(i, idx))]];
                end
              end
        in applyBang s (keys ctx1);

        let seq = SEQM(ctx1, f :: (List.tl forms), ASYN) in
        currentroot := ProofTree.update !currentroot seq;    
        rmacro suc
      end
      | _ -> failwith "Not expected subexponential while solving positive formulas."
    end

  | HBANG (sub, f) -> begin
    match Term.observe sub with
      | CONS (s) ->
        let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
        let seq = SEQM(prevctx, f :: (List.tl forms), ASYN) in
        currentroot := ProofTree.update !currentroot seq;  
        let idx = Hashtbl.find prevctx s in
        Constraints.add !constrs [[(Constraints.EMP(s, idx))]];
        rmacro suc
 
      | _ -> failwith "Not expected subexponential while solving positive formulas."
    end

  (* RULE: 1 *)
  | ONE -> 
    let ctx = getContexts (ProofTree.getConclusion !currentroot) in
    let idx = Hashtbl.find ctx "$gamma" in
    Constraints.add !constrs [[
      Constraints.EMP("$gamma", idx)
    ]];
    ProofTree.close !currentroot; 
    suc ()

  (* Atoms *)

  | COMP (ct, t1, t2) -> begin
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let sqnt = SEQM(prevctx, (COMP(ct, t1, t2)) :: (List.tl forms), SYNC) in
    currentroot := ProofTree.update !currentroot sqnt;
    ProofTree.close !currentroot;
    (*leaves := sqnt :: !leaves; *)
    (*ProofTree.addPremisse macrorule sqnt;*)
    suc ()
    end

  | ASGN (t1, t2) -> begin
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let sqnt = SEQM(prevctx, (ASGN(t1, t2)) :: (List.tl forms), SYNC) in
    currentroot := ProofTree.update !currentroot sqnt;
    ProofTree.close !currentroot;
    (*leaves := sqnt :: !leaves;*)
	(*ProofTree.addPremisse macrorule sqnt;*)
    suc ()
    end

  | PRINT (t1) -> suc () (* Nothing to do. *)

  (* G: Should these be considered?? *)
  (*
  | APP(head, arg1) -> 
    begin
      match (Norm.hnorm (APP( (Term.observe head), arg1))) with
      | f -> (match f with 
        | CONS(str) -> rmacro (PRED (str, CONS(str), NEG)) suc
        | APP(CONS(str3), arg2) -> rmacro (PRED (str3, APP(CONS(str3), arg2), NEG)) suc 
	      | _ -> failwith "ERROR!!"
      )
    end
  *)

  (* RULES: initial *)
  | PRED (str, terms, POS) -> begin
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let sqnt = SEQM(prevctx, (PRED(str, terms, POS)) :: (List.tl forms), SYNC) in
    currentroot := ProofTree.update !currentroot sqnt;
    ProofTree.close !currentroot;
    (*leaves := sqnt :: !leaves;*)
    let c = genInitCstrs prevctx (NOT((PRED(str, terms, POS)))) in
    Constraints.add !constrs c;
    suc ()
    end
  | NOT(PRED (str, terms, NEG)) -> begin
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let sqnt = SEQM(prevctx, (NOT((PRED(str, terms, NEG)))) :: (List.tl forms), SYNC) in
    currentroot := ProofTree.update !currentroot sqnt;
    ProofTree.close !currentroot;
    (*leaves := sqnt :: !leaves;*)
    let c = genInitCstrs prevctx (PRED(str, terms, NEG)) in
    Constraints.add !constrs c;
    suc ()
    end

  (* RULE: R arrow up *)
  | PRED (str, terms, NEG) -> begin
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let newctx = Hashtbl.copy prevctx in
    (* Constraints *)
    let i = Hashtbl.find !macroctx "$gamma" in
    let prev = Hashtbl.find prevctx "$gamma" in
    (* Updating global counter of s *)
    Hashtbl.remove !macroctx "$gamma";
    Hashtbl.add !macroctx "$gamma" (i+2);
    (* Creating the union constraints *)
    Constraints.add !constrs [[
      Constraints.ELIN(PRED(str, terms, NEG), ("$gamma", i+1));
      Constraints.UNION(("$gamma", prev), ("$gamma", i+1), ("$gamma", i+2))
      ]];
    (* Updating context index *)
    Hashtbl.remove newctx "$gamma";
    Hashtbl.add newctx "$gamma" (i+2);
    (* Creating new sequent and updating the proof tree *)
    let sqnt = SEQM(newctx, (List.tl forms), ASYN) in
    currentroot := ProofTree.update !currentroot sqnt;
    ProofTree.openproof !currentroot;
    rmacro suc
    end
  | NOT(PRED (str, terms, POS)) -> begin
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let newctx = Hashtbl.copy prevctx in
    (* Constraints *)
    let i = Hashtbl.find !macroctx "$gamma" in
    let prev = Hashtbl.find prevctx "$gamma" in
    (* Updating global counter of s *)
    Hashtbl.remove !macroctx "$gamma";
    Hashtbl.add !macroctx "$gamma" (i+2);
    (* Creating the union constraints *)
    Constraints.add !constrs [[
      Constraints.ELIN((NOT(PRED(str, terms, POS))), ("$gamma", i+1));
      Constraints.UNION(("$gamma", prev), ("$gamma", i+1), ("$gamma", i+2))
      ]];
    (* Updating context index *)
    Hashtbl.remove newctx "$gamma";
    Hashtbl.add newctx "$gamma" (i+2);
    (* Creating new sequent and updating the proof tree *)
    let sqnt = SEQM(newctx, (List.tl forms), ASYN) in
    currentroot := ProofTree.update !currentroot sqnt;
    ProofTree.openproof !currentroot;
    rmacro suc
    end

  | BRACKET(f) ->
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let sqnt = SEQM(prevctx, (Term.observe f) :: (List.tl forms), ASYN) in
    ProofTree.setConclusion !currentroot sqnt;
    rmacro suc

  | ABS(s, i, t) -> 
    let prevctx = getContexts (ProofTree.getConclusion !currentroot) in
    let sqnt = SEQM(prevctx, (apply_ptr (ABS(s,i,t))) :: (List.tl forms), ASYN) in
    ProofTree.setConclusion !currentroot sqnt;
    rmacro suc

  | h -> print_term h; failwith " Macro not implemented for this case."
   
  with 
    (* Empty goals, finish macro. *)
    | Failure "hd" -> 
      (*let seq = ProofTree.getConclusion !currentroot in*)
      (*leaves := seq :: !leaves;*)
      suc ()
    | Failure st -> failwith st

;;

