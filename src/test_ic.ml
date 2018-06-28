open OUnit2
open Bipole
open Context
open ProofTree
open Subexponentials
open Specification
open Prints
open OlRule
open ProofTreeSchema
open Permutation

let initAll () = 
  Context.initialize ();
  Subexponentials.initialize ();
;;
let position lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let file = curr.Lexing.pos_fname in
  let line = curr.Lexing.pos_lnum in
  let char = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    if file = "" then
      () (* lexbuf information is rarely accurate at the toplevel *)
    else
      print_string ""; Format.sprintf ": line %d, character %d" line char

let parse file_name =
  let file_sig = open_in (file_name^".sig") in
  let lexbuf = Lexing.from_channel file_sig in
  try
    let (kt, tt) = Parser.signature Lexer.token lexbuf in
      let file_prog = open_in (file_name^".pl") in 
      let lexbuf = Lexing.from_channel file_prog in
      try
        let (s, c, i, a) = Parser.specification Lexer.token lexbuf in
          Specification.create (kt, tt, s, c, i, a)
      with
      | Parsing.Parse_error -> failwith ("Syntax error while parsing .pl file: " ^ (position lexbuf))
      | Failure str -> failwith ("[ERROR] " ^ (position lexbuf))
  with
  | Parsing.Parse_error -> failwith ("Syntax error while parsing .sig file: " ^ (position lexbuf))
  | Failure _ -> failwith ("[ERROR] " ^ (position lexbuf))
;;

(* Test initial coherence *)

let test1_ic test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/g1m" in
  let spec = parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.initialCoherence specName spec);;

let test2_ic test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/lal" in
  let spec = parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.initialCoherence specName spec);;

let test3_ic test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/lj" in
  let spec = parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.initialCoherence specName spec);;

let test4_ic test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/lk" in
  let spec = parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.initialCoherence specName spec);;

let test5_ic test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/ll" in
  let spec = parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.initialCoherence specName spec);;


let test6_ic test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/ill" in
  let spec = parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.initialCoherence specName spec);;

let test7_ic test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/mlj" in
  let spec = parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.initialCoherence specName spec);;

let test8_ic test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/s4" in
  let spec = parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.initialCoherence specName spec);;

let test9_ic test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/g3k" in
  let spec = parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.initialCoherence specName spec);;

let test10_ic test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/lax" in
  let spec = parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.initialCoherence specName spec);;

