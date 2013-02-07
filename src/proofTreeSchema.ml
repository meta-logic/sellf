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
open Constraints
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

(* Updates the tree with a new premisse and returns a reference to this new
child *)
let update pt sq = let newc = create sq in
  pt.premises <- newc :: pt.premises; newc

let clearPremises pt = pt.premises <- []

(* Implement LL rules here! :) *)
(* Each rule returns one or two proof trees and a constraintset, except if they
have no premises (initial and top) *)

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
  let newgoals1 = f1::(List.filter (fun form -> form != f) goals) in
  let newgoals2 = f2::(List.filter (fun form -> form != f) goals) in
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
  let newgoals = f1::f2::(List.filter (fun form -> form != f) goals) in
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
  let newf = Norm.hnorm (APP (ABS (s, 1, f), [new_var])) in
  let newgoals = f1::(List.filter (fun form -> form != f) goals) in
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

