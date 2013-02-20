(**************************************)
(*                                    *)
(*  Proof tree with context variables *)
(*  (instead of real contexts)        *)
(*                                    *)
(*  Giselle Machado Reis              *)
(*  2013                              *)
(*                                    *)
(**************************************)

open Sequent
open Context
open Term
open Llrules

type prooftree = {
  conclusion : SequentSchema.sequent;
  mutable premises : prooftree list;
  mutable rule : llrule option
}

let create sq = {
  conclusion = sq;
  premises = [];
  rule = NONE
}

let getConclusion pt = pt.conclusion

(* TODO: check if this actually copies a prooftree *)
let rec copy pt = 
  let cp = create pt.conclusion in
  cp.rule <- pt.rule;
  let rec cpPremises lst = match lst with
    | [] -> []
    | p :: t -> (copy p) :: cpPremises t
  in
  cp.premises <- (cpPremises pt.premises);
  cp

let rec getOpenLeaves pt = match pt.rule with
  | SOME(r) -> List.flatten (List.map (fun p -> getOpenLeaves p) pt.premises)
  | NONE -> [pt.conclusion]

let rec printOpenLeaves pt = match pt.rule with
  | SOME(r) -> List.iter (fun p -> printOpenLeaves p) pt.premises
  | NONE -> print_endline( SequentSchema.toString pt.conclusion )

(* Implement LL rules here! :) *)
(* Each rule returns one or two proof trees and a constraintset, except if they
have no premises (initial, top and one) *)

let decide pt f subexp = 
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let reqconstr = Constraints.requireIn f subexp ctx in
  let newctx = ContextSchema.next ctx subexp in
  let remconstr = Constraints.remove f subexp ctx newctx in
  (* Create a new sequent and add this as a premise to the prooftree *)
  let premise = SequentSchema.createSync newctx f in
  let newpt = create premise in
  pt.rule <- SOME(DECIDE);
  pt.premises <- [newpt];
  (newpt, Constraints.union reqconstr remconstr) 

let releaseDown pt = 
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let goals = SequentSchema.getGoals conc in
  let newctx = ContextSchema.copy ctx in
  let premise = SequentSchema.createAsyn newctx goals in
  let newpt = create premise in
  pt.rule <- SOME(RELEASEDOWN);
  pt.premises <- [newpt];
  (newpt, Constraints.create [])

let releaseUp pt f = 
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let goals = SequentSchema.getGoals conc in
  let newctx = ContextSchema.insert ctx "$gamma" in
  let insertcstr = Constraints.insert f "$gamma" ctx newctx in
  let newgoals = List.filter (fun form -> form != f) goals in
  let premise = SequentSchema.createAsyn newctx newgoals in
  let newpt = create premise in
  pt.rule <- SOME(RELEASEUP);
  pt.premises <- [newpt];
  (newpt, insertcstr)

let applyWith pt f =
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let goals = SequentSchema.getGoals conc in
  let newctx1 = ContextSchema.copy ctx in
  let newctx2 = ContextSchema.copy ctx in
  let f1, f2 = match Term.observe f with 
    | WITH(f1, f2) -> f1, f2
    | _ -> failwith "Wrong formula in rule application."
  in
  let newgoals1 = f1 :: (List.filter (fun form -> form != f) goals) in
  let newgoals2 = f2 :: (List.filter (fun form -> form != f) goals) in
  let premise1 = SequentSchema.createAsyn newctx1 newgoals1 in
  let premise2 = SequentSchema.createAsyn newctx2 newgoals2 in
  let newpt1 = create premise1 in
  let newpt2 = create premise2 in
  pt.rule <- SOME(WITHRULE);
  pt.premises <- [newpt1; newpt2];
  ((newpt1, newpt2), Constraints.create [])

let applyParr pt f = 
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let goals = SequentSchema.getGoals conc in
  let newctx = ContextSchema.copy ctx in
  let f1, f2 = match Term.observe f with 
    | PARR(f1, f2) -> f1, f2 
    | _ -> failwith "Wrong formula in rule application."
  in
  let newgoals = f1 :: f2 :: (List.filter (fun form -> form != f) goals) in
  let premise = SequentSchema.createAsyn newctx newgoals in
  let newpt = create premise in
  pt.rule <- SOME(PARRRULE);
  pt.premises <- [newpt];
  (newpt, Constraints.create [])

let applyQst pt f =
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let goals = SequentSchema.getGoals conc in
  let subexp, f1 = match Term.observe f with 
    | QST(CONS(s), f1) -> s, f1
    | _ -> failwith "Wrong formula in rule application."
  in
  let newctx = ContextSchema.insert ctx subexp in
  let insertcstr = Constraints.insert f1 subexp ctx newctx in
  let newgoals = List.filter (fun form -> form != f) goals in
  let premise = SequentSchema.createAsyn newctx newgoals in
  let newpt = create premise in
  pt.rule <- SOME(QSTRULE);
  pt.premises <- [newpt];
  (newpt, insertcstr)

let applyForall pt f = 
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let goals = SequentSchema.getGoals conc in
  let s, i, f1 = match Term.observe f with
    | FORALL(s, i, f1) -> s, i, f1
    | _ -> failwith "Wrong formula in rule application."
  in
  let newctx = ContextSchema.copy ctx in
  Term.varid := !Term.varid + 1;
  let new_var = VAR ({str = s; id = !varid; tag = Term.EIG; ts = 0; lts = 0}) in
  let newf = Norm.hnorm (APP (ABS (s, 1, f1), [new_var])) in
  let newgoals = newf :: (List.filter (fun form -> form != f) goals) in
  let premise = SequentSchema.createAsyn newctx newgoals in
  let newpt = create premise in
  pt.rule <- SOME(FORALLRULE);
  pt.premises <- [newpt];
  (newpt, Constraints.create [])

(* GR: Do we need to create any constraints for the T rule? *)
let applyTop pt = pt.rule <- SOME(TOPRULE)

let applyBot pt f = 
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let goals = SequentSchema.getGoals conc in
  let newctx = ContextSchema.copy ctx in
  let newgoals = List.filter (fun form -> form != f) goals in
  let premise = SequentSchema.createAsyn newctx newgoals in
  let newpt = create premise in
  pt.rule <- SOME(BOTRULE);
  pt.premises <- [newpt];
  (newpt, Constraints.create [])

(* GR TODO assert that the main formulas are the only ones in the goals of
synchronous phase?? *)

let applyOne pt =
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  pt.rule <- SOME(ONERULE);
  Constraints.empty "$gamma" ctx

let applyInitial pt f = 
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let initcstr = Constraints.initial ctx f in
  pt.rule <- SOME(INIT);
  initcstr

let applyAddOr1 pt f = 
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let newctx = ContextSchema.copy ctx in
  let f1 = match Term.observe f with
    | ADDOR(f1,_) -> f1
    | _ -> failwith "Wrong formula in rule application."
  in
  let premise = SequentSchema.createSync newctx f1 in
  let newpt = create premise in
  pt.rule <- SOME(ADDOR1RULE);
  pt.premises <- [newpt];
  (newpt, Constraints.create [])

let applyAddOr2 pt f = 
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let newctx = ContextSchema.copy ctx in
  let f2 = match Term.observe f with
    | ADDOR(_,f2) -> f2
    | _ -> failwith "Wrong formula in rule application."
  in
  let premise = SequentSchema.createSync newctx f2 in
  let newpt = create premise in
  pt.rule <- SOME(ADDOR2RULE);
  pt.premises <- [newpt];
  (newpt, Constraints.create [])

let applyExists pt f = 
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let s, i, f1 = match Term.observe f with
    | EXISTS(s, i, f1) -> s, i, f1
    | _ -> failwith "Wrong formula in rule application."
  in
  let newctx = ContextSchema.copy ctx in
  Term.varid := !Term.varid + 1;
  let new_var = V ({str = s; id = !varid; tag = Term.LOG; ts = 0; lts = 0}) in
  let ptr = PTR {contents = new_var} in
  let newf = Norm.hnorm (APP (ABS (s, 1, f1), [ptr])) in
  let premise = SequentSchema.createSync newctx newf in
  let newpt = create premise in
  pt.rule <- SOME(EXISTSRULE);
  pt.premises <- [newpt];
  (newpt, Constraints.create [])

let applyTensor pt f = 
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let f1, f2 = match Term.observe f with
    | TENSOR(f1, f2) -> f1, f2
    | _ -> failwith "Wrong formula in rule application."
  in
  let (newctx1, newctx2) = ContextSchema.split ctx in
  let splitcstr = Constraints.split ctx newctx1 newctx2 in
  let premise1 = SequentSchema.createSync newctx1 f1 in
  let premise2 = SequentSchema.createSync newctx2 f2 in
  let newpt1 = create premise1 in
  let newpt2 = create premise2 in
  pt.rule <- SOME(TENSORRULE);
  pt.premises <- [newpt1; newpt2];
  ((newpt1, newpt2), splitcstr)

let applyBang pt f = 
  let conc = getConclusion pt in
  let ctx = SequentSchema.getContext conc in
  let s, f1 = match Term.observe f with
    | BANG(CONS(s), f1) -> s, f1
    | _ -> failwith "Wrong formula in rule application."
  in
  let newctx = ContextSchema.bang ctx s in
  let bangcstr = Constraints.bang newctx s in
  let premise = SequentSchema.createAsyn newctx [f1] in
  let newpt = create premise in
  pt.rule <- SOME(BANGRULE);
  pt.premises <- [newpt];
  (newpt, bangcstr)


