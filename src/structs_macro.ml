open Term
open Prints
open Structs
open ProofTree
open Constraints

let macrorule = ref (ProofTree.create EMPSEQ) ;;
let macrolst : (ProofTree.prooftree * Constraints.constraints) list ref = ref [] ;;
let currentroot : ProofTree.prooftree ref = ref !macrorule ;;
let constrs = ref (Constraints.create ()) ;;

(* List to save the premisses for the curret macro rule *)
(*let leaves : (sequent list) ref = ref [] ;;*)

let sqntcounter = ref 1 ;;

(* Stores all the rules for the generation of the macros *)
let rules : (terms list) ref = ref [] ;;

(* The context of the macro rule will save the name of the subexponential and
its "version" (starting from 0) *)
let macroctx : (string, int) Hashtbl.t ref = ref (Hashtbl.create 100) ;;

let getContexts seq = match seq with
  | SEQM(ctx, _, _) -> ctx
  | EMPSEQ -> failwith "Previous sequent is the empty one."
  | SEQ(_, _, _) -> failwith "Using wrong type of sequent for macro rules."
;;

let initMacroCtx () = 
  let rec initialize lst = match lst with
    | [] -> ()
    | h::t -> Hashtbl.remove !macroctx h; Hashtbl.add !macroctx h 0; initialize t
  in initialize (keys subexTpTbl)
;;

(* Initialize fresh macro *)
let initMacro formula =
  (*leaves := [];*)
  sqntcounter := 1;
  Constraints.clear !constrs;
  initMacroCtx ();
  let seq = SEQM(Hashtbl.copy !macroctx, formula :: [], SYNC) in
    ProofTree.setConclusion !macrorule seq;
    ProofTree.setPremisses !macrorule [];
    currentroot := !macrorule
;;

(* Initialize a macro rule from a predefined leaf in a tree *)
let initMacroFrom pt leaf cstr formula =
  macrorule := pt;
  (*let leaves = ProofTree.getOpenLeaves pt in
  let leaf = List.nth leaves leafn in*)
  let ctx = getContexts (ProofTree.getConclusion leaf) in
  let seq = SEQM(ctx, formula::[], SYNC) in
  currentroot := ProofTree.update leaf seq;
  constrs := Constraints.copy cstr
;;

(*
let initMacroArgs lvs cstr ctx ctxnums formula = 
  leaves := lvs;
  sqntcounter := 1;
  constrs := Constraints.copy cstr;
  macroctx := Hashtbl.copy ctxnums;
  let seq = SEQM(ctx, formula::[], SYNC) in
    ProofTree.setConclusion !macrorule seq;
    ProofTree.setPremisses !macrorule [];
    currentroot := !macrorule
;;
*)

let save_macro () = 
  let m = ProofTree.copy !macrorule in
  let c = Constraints.copy !constrs in
  macrolst := (m, c) :: !macrolst ;;

(*
(* G: Not printing the context. *)
let print_sequent sq = match sq with
| SEQM(_, [], _)
| SEQ(_, [], _) ->
  print_string "Sequent "; 
  print_int !sqntcounter; sqntcounter := !sqntcounter + 1; print_newline ();
  print_string "--> Open sequent";
  print_newline ();
  flush stdout;

| SEQM(_, t :: tl, _) 
| SEQ(_, t :: tl, _) -> 
  print_string "Sequent "; 
  print_int !sqntcounter; sqntcounter := !sqntcounter + 1; print_newline ();
  (*print_hashtbl k; print_newline ();*)
  print_string "--> Closed sequent with initial rule on: "; print_term t;
  print_newline ();
  flush stdout;

| _ -> print_string "Unexpected sequent."; flush stdout
;;

let rec print_leaves p = match p with
| [] -> sqntcounter := 1; print_string "End of macro rule.\n\n"
| hd :: tl -> print_sequent hd; print_leaves tl
;;
*)
