(**************************************)
(*                                    *)
(*             Sequent                *)
(*                                    *)
(*  Giselle Machado Reis              *)
(*  2013                              *)
(*                                    *)
(**************************************)

(* TODO: write interface *)
(* TODO: rewrite printing methods *)

type phase = SYNC | ASYN

type abstractSeq = {
  contextAbs : context; 
  goalsAbs : term list;
  polarityAbs : phase;
}

type concreteSeq = {
  mutable contextIn : context;
  mutable contextOut : context;
  goalsConc : term list;
  polarityConc : phase;
}

type sequent = 
  | ABSSEQ of abstractSequent
  | CONSEQ of concreteSequent

(* I don't like that there are that many create methods for sequents, but this
 * avoids errors by checking the sequents created on compilation time. Also,
 * there must me one for each type of sequent... *)
let createSyncConcrete ctxIn ctxOut goal = {
  contextIn = ctxIn;
  contextOut = ctxOut;
  goalsConc = [goal];
  polarityConc = SYNC;
}

let createAsynConcrete ctxIn ctxOut goals = {
  contextIn = ctxIn;
  contextOut = ctxOut;
  goalsConc = goals;
  polarityConc = ASYN;
}

let createSyncAbstract ctx goal = {
  contextAbs = ctx;
  goalsAbs = [goal];
  polarityAbs = SYNC;
}

let createAsynAbstract ctx goals = {
  contextAbs = ctx;
  goalsAbs = goals;
  polarityAbs = ASYN;
}

let getGoals seq = match seq with
  | ABSSEQ(s) => s.goalsAbs
  | CONSEQ(s) => s.goalsConc

let getContext seq = match seq with
  | ABSSEQ(s) => s.contextAbs
  | CONSEQ(s) => failwith "Do you want the context in or out?"

let getContextIn seq = match seq with
  | ABSSEQ(s) => failwith "No context in for abstract sequent."
  | CONSEQ(s) => s.contextIn

let getContextOut seq = match seq with
  | ABSSEQ(s) => failwith "No context out for abstract sequent."
  | CONSEQ(s) => s.contextOut

let getPhase seq = match seq with
  | ABSSEQ(s) => s.polarityAbs
  | CONSEQ(s) => s.polarityConc


