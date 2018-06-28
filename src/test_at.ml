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

(* test atomicelim *)
let test1_at test_ctxt = 
  initAll();
  let spec = parse "../examples/proofsystems/g1m" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test2_at test_ctxt = 
  initAll();
  let spec = parse "../examples/proofsystems/lal" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test3_at test_ctxt = 
  initAll();
  let spec = parse "../examples/proofsystems/lax" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test4_at test_ctxt = 
  initAll();
  let spec = parse "../examples/proofsystems/lj" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test5_at test_ctxt = 
  initAll();
  let spec = parse "../examples/proofsystems/lk" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test6_at test_ctxt = 
  initAll();
  let spec = parse "../examples/proofsystems/ll" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test7_at test_ctxt = 
  initAll();
  let spec = parse "../examples/proofsystems/ill" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test8_at test_ctxt = 
  initAll();
  let spec = parse "../examples/proofsystems/mlj" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;; 

let test9_at test_ctxt = 
  initAll();
  let spec = parse "../examples/proofsystems/s4" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;; 

let test10_at test_ctxt = 
  initAll();
  let spec = parse "../examples/proofsystems/g3k" in
  assert_equal false (Staticpermutationcheck.weak_coherent spec)
;;

