(**************************************)
(*                                    *)
(*           Proof tree               *)
(*                                    *)
(*  Giselle Machado Reis              *)
(*  2013                              *)
(*                                    *)
(**************************************)

open Term 
open Prints
open Llrules
open Sequent

let counter = ref 0 ;;

(* Declare mutable so I can modify directly on the object *)
type prooftree = {
  mutable conclusion : Sequent.sequent;
  mutable premises : prooftree list;
  mutable closed : bool; (* TODO remove this field *)
  mutable rule : llrule option
}

let create sq = {
  conclusion = sq;
  premises = [];
  rule = None;
  closed = true (* for printing purposes... fixme later *)
}

let getConclusion pt = pt.conclusion

let getPremises pt = pt.premises

(* Application of LL rules *)
(* Each rule returns one or two prooftrees and a function that determines how
the premises out-contexts are copied to the conclusion top-down *)

(* NEW

let releaseDown pt = 
  let inCtx = Sequent.getContextIn pt.conclusion in
  let goals = Sequent.getGoals in
  let ctx = Context.copy inCtx in
  let premise = Sequent.createAsyn ctx goals in
  let newpt = create premise in
  pt.rule <- Some(RELEASEDOWN);
  pt.premises <- [newpt];
  newpt

let releaseUp pt f = 
  let ctx = Sequent.getContextIn pt.conclusion in
  let goals = Sequent.getGoals conc in
  let newctx = Context.add ctx "$gamma" in
  let newgoals = List.filter (fun form -> form != f) goals in
  let premise = Sequent.createAsyn newctx newgoals in
  let newpt = create premise in
  pt.rule <- Some(RELEASEUP);
  pt.premises <- [newpt];
  newpt
  
let applyAddOr1 pt f = 
  let ctx = Sequent.getContextIn pt.conclusion in
  let newctx = Context.copy ctx in
  let f1 = match Term.observe f with
    | ADDOR(f1,_) -> f1
    | _ -> failwith "Wrong formula in rule application."
  in
  let premise = Sequent.createSync newctx f1 in
  let newpt = create premise in
  pt.rule <- Some(ADDOR1RULE);
  pt.premises <- [newpt];
  newpt

let applyAddOr2 pt f = 
  let ctx = Sequent.getContextIn pt.conclusion in
  let newctx = Context.copy ctx in
  let f2 = match Term.observe f with
    | ADDOR(_,f2) -> f2
    | _ -> failwith "Wrong formula in rule application."
  in
  let premise = Sequent.createSync newctx f2 in
  let newpt = create premise in
  pt.rule <- Some(ADDOR2RULE);
  pt.premises <- [newpt];
  newpt

(* Created the left premise for the tensor rule *)
let applyTensor1 pt f = 
  let ctx = Sequent.getContextIn pt.conclusion in
  let f1 = match Term.observe f with
    | TENSOR(f1,_) -> f1
    | _ -> failwith "Wrong formula in rule application."
  in
  let newctx = Context.copy ctx in
  let premise = Sequent.createSync newctx f1 in
  let newpt = create premise in
  pt.rule <- Some(TENSORRULE);
  pt.premises <- [newpt];
  newpt

(* Creates the right premise for the tensor rule by copying the out-context of
the left premise. *)
let applyTensor2 pt f = 
  let sibling = match pt.premises with
    | [p] -> p.conclusion
    | _ -> failwith "Invalid premise setting for tensor rule."  
  in
  let ctx = Sequent.getContextOut sibling in
  let f2 = match Term.observe f with
    | TENSOR(_,f2) -> f2
    | _ -> failwith "Wrong formula in rule application."
  in
  let newctx = Context.copy ctx in
  let premise = Sequent.createSync newctx f2 in
  let newpt = create premise in
  pt.premises <- pt.premises @ [newpt];
  newpt

let applyExists pt f = 
  let ctx = Sequent.getContextIn pt.conclusion in
  let s, i, f1 = match Term.observe f with
    | EXISTS(s, i, f1) -> s, i, f1
    | _ -> failwith "Wrong formula in rule application."
  in
  let newctx = Context.copy ctx in
  Term.varid := !Term.varid + 1;
  let new_var = V ({str = s; id = !varid; tag = Term.LOG; ts = 0; lts = 0}) in
  let ptr = PTR {contents = new_var} in
  let newf = Norm.hnorm (APP (ABS (s, 1, f1), [ptr])) in
  let premise = Sequent.createSync newctx newf in
  let newpt = create premise in
  pt.rule <- Some(EXISTSRULE);
  pt.premises <- [newpt];
  newpt

let applyOne pt = pt.rule <- Some(ONERULE)

let applyBang pt f = 
  let ctx = SequentSchema.getContext pt.conclusion in
  let s, f1 = match Term.observe f with
    | BANG(CONS(s), f1) -> s, f1
    | _ -> failwith "Wrong formula in rule application."
  in
  let newctx = Context.bangin ctx s in
  let premise = Sequent.createAsyn newctx [f1] in
  let newpt = create premise in
  pt.rule <- Some(BANGRULE);
  pt.premises <- [newpt];
  newpt 

let applyWith pt f =
  let ctx = Sequent.getContextIn pt.conclusion in
  let goals = Sequent.getGoals pt.conclusion in
  let newctx1 = Context.copy ctx in
  let newctx2 = Context.copy ctx in
  let f1, f2 = match Term.observe f with 
    | WITH(f1, f2) -> f1, f2
    | _ -> failwith "Wrong formula in rule application."
  in
  let newgoals1 = f1 :: (List.filter (fun form -> form != f) goals) in
  let newgoals2 = f2 :: (List.filter (fun form -> form != f) goals) in
  let premise1 = Sequent.createAsyn newctx1 newgoals1 in
  let premise2 = Sequent.createAsyn newctx2 newgoals2 in
  let newpt1 = create premise1 in
  let newpt2 = create premise2 in
  pt.rule <- Some(WITHRULE);
  pt.premises <- [newpt1; newpt2];
  (newpt1, newpt2)

let applyParr pt f = 
  let ctx = Sequent.getContextIn pt.conclusion in
  let goals = Sequent.getGoals pt.conclusion in
  let newctx = Context.copy ctx in
  let f1, f2 = match Term.observe f with 
    | PARR(f1, f2) -> f1, f2 
    | _ -> failwith "Wrong formula in rule application."
  in
  let newgoals = f1 :: f2 :: (List.filter (fun form -> form != f) goals) in
  let premise = Sequent.createAsyn newctx newgoals in
  let newpt = create premise in
  pt.rule <- Some(PARRRULE);
  pt.premises <- [newpt];
  newpt

let applyTop pt =
  Context.markErasable (Sequent.getContextIn pt.conclusion);
  pt.rule <- Some(TOPRULE)

let applyBot pt f = 
  let ctx = Sequent.getContextIn pt.conclusion in
  let goals = Sequent.getGoals pt.conclusion in
  let newctx = Context.copy ctx in
  let newgoals = List.filter (fun form -> form != f) goals in
  let premise = Sequent.createAsyn newctx newgoals in
  let newpt = create premise in
  pt.rule <- Some(BOTRULE);
  pt.premises <- [newpt];
  newpt

let applyForall pt f = 
  let ctx = Sequent.getContextIn pt.conclusion in
  let goals = Sequent.getGoals pt.conclusion in
  let s, i, f1 = match Term.observe f with
    | FORALL(s, i, f1) -> s, i, f1
    | _ -> failwith "Wrong formula in rule application."
  in
  let newctx = Context.copy ctx in
  Term.varid := !Term.varid + 1;
  let new_var = VAR ({str = s; id = !varid; tag = Term.EIG; ts = 0; lts = 0}) in
  let newf = Norm.hnorm (APP (ABS (s, 1, f1), [new_var])) in
  let newgoals = newf :: (List.filter (fun form -> form != f) goals) in
  let premise = Sequent.createAsyn newctx newgoals in
  let newpt = create premise in
  pt.rule <- Some(FORALLRULE);
  pt.premises <- [newpt];
  newpt

let applyQst pt f =
  let ctx = Sequent.getContextIn pt.conclusion in
  let goals = Sequent.getGoals pt.conclusion in
  let subexp, f1 = match Term.observe f with 
    | QST(CONS(s), f1) -> s, f1
    | _ -> failwith "Wrong formula in rule application."
  in
  let newctx = Context.add ctx subexp in
  let newgoals = List.filter (fun form -> form != f) goals in
  let premise = Sequent.createAsyn newctx newgoals in
  let newpt = create premise in
  pt.rule <- Some(QSTRULE);
  pt.premises <- [newpt];
  newpt

*)

(*let setConclusion pt c = pt.conclusion <- c*)

let setPremises pt p = pt.premises <- p
(*let getPremises pt = pt.premises*)

(*
let addPremise pt p = let newc = create p in
  pt.premises <- newc :: pt.premises

let getLatestPremise pt = try List.hd pt.premises 
  with Failure "hd" -> failwith "[ERROR] This sequent has no premisses."
*)

let rec copy pt = let cp = create pt.conclusion in
  let rec cpPremises lst = match lst with
    | [] -> []
    | p::t -> (copy p) :: cpPremises t
  in
  setPremises cp (cpPremises pt.premises); cp

(* Updates the tree with a new premisse and returns a reference to this new
child *)
let update pt sq = let newc = create sq in
  pt.premises <- newc :: pt.premises; newc

let close pt = pt.closed <- true

let openproof pt = pt.closed <- false

let rec getLeaves pt = List.fold_right (fun el acc -> 
  match el.premises with
    | [] -> el :: acc
    | _ -> getLeaves el @ acc
  ) pt.premises []

(*
    let rec getOpenLeaves pt = List.fold_right (fun el acc -> 
      match el.premisses with
        | [] -> if is_open el.conclusion then el :: acc else acc
        | _ -> getOpenLeaves el @ acc
      ) pt.premisses []
*)

(*
    let rec getOpenLeaves pt = List.fold_right (fun el acc ->
      if not el.closed then el :: acc
      else getOpenLeaves el @ acc
      ) pt.premisses []
*)

let rec toTexString pt = match pt.closed with
  | true ->
    let topproof = match pt.premises with
      | [] -> ""
      | hd::tl -> (toTexString hd)^(List.fold_right (fun el acc -> "\n&\n"^(toTexString el)) tl "") 
    in
    (*"\\infer{"^(Sequent.toTexString (getConclusion pt))^"}\n{"^topproof^"}"*)
    "\\cfrac{"^topproof^"}\n{"^(Sequent.toTexString (getConclusion pt))^"}"
  (* An open proof has no premisses. *)
  | false -> (Sequent.toTexString (getConclusion pt))
      

