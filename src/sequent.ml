(* Giselle Machado Reis - 2012 *)

(************************** SEQUENTS ************************)

open Context
open ContextSchema
open Types
open Prints

type phase = 
  | ASYN
  | SYNC

let print_phase p = match p with
  | ASYN -> print_string "asyn"
  | SYNC -> print_string "sync"
;;

module type SEQUENT =
  sig
  
    type sequent = {
      mutable ctxin : Context.context;
      mutable ctxout : Context.context;
      mutable goals : terms list;
      pol : phase }
    val getPhase : sequent -> phase
    val getGoals : sequent -> terms list
    val create : unit -> sequent
    val create : phase -> sequent
    val create : Context.context -> Context.context -> terms list -> phase -> sequent
    val setGoal : sequent -> terms -> unit
    val setGoals : sequent -> terms list -> unit
    val setCtxIn : sequent -> Context.context -> unit
    val getCtxIn : sequent -> Context.context
    val setCtxOut : sequent -> Context.context -> unit
    val getCtxOut : sequent -> Context.context
    val addGoal : sequent -> terms -> unit
    val toString : sequent -> string
    val toTexString : sequent -> string
    
  end

module Sequent : SEQUENT = struct

  type sequent = {
    mutable ctxin : Context.context;
    mutable ctxout : Context.context (*option NEW *);
    mutable goals : terms list;
    pol : phase
  }

(* NEW 

  let createAsyn ctxIn formulas = {
    ctxin = ctxIn;
    ctxout = NONE;
    goals = formulas;
    pol = ASYN
  }

  let createSync ctxIn formula = {
    ctxin = ctxIn;
    ctxout = NONE;
    goals = [formula];
    pol = SYNC
  }
*)

  let getPhase seq = seq.pol

  let getGoals seq = seq.goals

(* NEW
  let setContextOut seq oc = seq.ctxout <- SOME(oc)

  let getContextOut seq = match seq.ctxout with
    | SOME(ctx) -> ctx
    | NONE -> failwith "Out-context not set. Impossible to get."
*)

(*** OLD ****)

  let create () = {
    ctxin = Context.createEmpty ();
    ctxout = Context.createEmpty ();
    goals = [];
    pol = SYNC
  }

  let create phase = {
    ctxin = Context.createEmpty ();
    ctxout = Context.createEmpty ();
    goals = [];
    pol = phase;
  }

  let create ci co lf ph = {
    ctxin = ci;
    ctxout = co;
    goals = lf;
    pol = ph
  }

  let setGoal seq f = seq.goals <- [f]
  let setGoals seq lf = seq.goals <- lf

  let setCtxIn seq ic = seq.ctxin <- ic
  let getCtxIn seq = seq.ctxin

  let setCtxOut seq oc = seq.ctxout <- oc
  let getCtxOut seq = seq.ctxout

  let addGoal seq f = seq.goals <- f::seq.goals

(*
  let isEqual s1 s2 = match s1, s2 with
    | SEQ(ht1, tl1, ph1), SEQ(ht2, tl2, ph2) -> ht1 = ht2 && tl1 = tl2 && ph1 = ph2 
    | SEQM(ht1, tl1, ph1), SEQM(ht2, tl2, ph2) -> ht1 = ht2 && tl1 = tl2 && ph1 = ph2 
    | EMPSEQ, EMPSEQ -> true
    | _, _ -> false
*)

  let toString seq = match seq.pol with
    | ASYN -> "K : Γ ⇑ "^(termsListToString seq.goals)
    | SYNC -> "K : Γ ⇓ "^(termsListToString seq.goals)

  let toTexString seq = match seq.pol with
    | ASYN -> ("\\mathcal{K} : \\Gamma \\Uparrow "^(termsListToTexString seq.goals) )
    | SYNC -> ("\\mathcal{K} : \\Gamma \\Downarrow "^(termsListToTexString seq.goals) )

  end
;;

module type SEQUENTSCHEMA = 
  sig 
  
    type sequent = {
    mutable ctx : ContextSchema.context;
    goals : terms list;
    pol : phase }
    val createSync : ContextSchema.context -> terms -> sequent
    val createAsyn : ContextSchema.context -> terms list -> sequent
    val getPhase : sequent -> phase
    val getGoals : sequent -> terms list
    val getContext : sequent -> ContextSchema.context
    val toString : sequent -> string
    val toTexString : sequent -> string
    
  end

module SequentSchema : SEQUENTSCHEMA = struct
 
  (* Sequent has contexts in and out. This has only one generic context. *)
  type sequent = {
    mutable ctx : ContextSchema.context;
    goals : terms list;
    pol : phase;
  }

  (* Initializes a sequent with a specific context and one goal *)
  let createSync context formula = {
    ctx = context;
    goals = [formula];
    pol = SYNC;
  }
  
  (* Initializes a sequent with a specific context, one goal and a phase *)
  let createAsyn context formulas = {
    ctx = context;
    goals = formulas;
    pol = ASYN;
  }
 
  let getPhase seq = seq.pol

  let getGoals seq = seq.goals

  let getContext seq = seq.ctx

  let toString seq = match seq.pol with
    | ASYN -> ContextSchema.toString seq.ctx ^ " ⇑ " ^ (termsListToString seq.goals)
    | SYNC -> ContextSchema.toString seq.ctx ^ " ⇓ " ^ (termsListToString seq.goals)

  let toTexString seq = match seq.pol with
    | ASYN -> ContextSchema.toTexString seq.ctx ^ " \\Uparrow " ^ (termsListToTexString seq.goals)
    | SYNC -> ContextSchema.toTexString seq.ctx ^ " \\Downarrow " ^ (termsListToTexString seq.goals)

  end
;;
