open OUnit2
open Bipole
open Context
open ProofTree
open Subexponentials
open Prints
open OlRule
open ProofTreeSchema
open Permutation

let initAll () = 
  Specification.initialize ();
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

let parse file_name = begin
  let file_sig = open_in (file_name^".sig") in
  let lexbuf = Lexing.from_channel file_sig in
  begin
    try 
      while true do
        let _ = Parser.types Lexer.token lexbuf in ();
      done; true
    with 
      | Lexer.Eof -> 
         let file_prog = open_in (file_name^".pl") in 
         let lexbuf = Lexing.from_channel file_prog in
           begin
           try
             while true do
               let _ = Parser.specification Lexer.token lexbuf in ();
             done; true 
           with
             | Lexer.Eof -> true
             | Parsing.Parse_error ->  Format.printf "Syntax error while parsing .pl file%s.\n%!" (position lexbuf); false
             | Failure str -> Format.printf ("ERROR:%s\n%!") (position lexbuf); print_endline str; false
           end
      | Parsing.Parse_error ->  Format.printf "Syntax error while parsing .sig file%s.\n%!" (position lexbuf); false
      | Failure _ -> Format.printf "Syntax error%s.\n%!" (position lexbuf); false
    end
end ;;

let check_atomicelim () = begin
  if Staticpermutationcheck.weak_coherent () then true else false 
end ;;

(* test atomicelim *)
let test1_at test_ctxt = 
  initAll();
  parse "../examples/proofsystems/g1m";
  assert_equal true (check_atomicelim ())
;;

let test2_at test_ctxt = 
  initAll();
  parse "../examples/proofsystems/lal";
  assert_equal true (check_atomicelim ())
;; 

let test3_at test_ctxt = 
  initAll();
  parse "../examples/proofsystems/lax";
  assert_equal true (check_atomicelim ())
;; 

let test4_at test_ctxt = 
  initAll();
  parse "../examples/proofsystems/lj";
  assert_equal true (check_atomicelim ())
;; 

let test5_at test_ctxt = 
  initAll();
  parse "../examples/proofsystems/lk";
  assert_equal true (check_atomicelim ())
;; 

let test6_at test_ctxt = 
  initAll();
  parse "../examples/proofsystems/ll";
  assert_equal true (check_atomicelim ())
;; 

let test7_at test_ctxt = 
  initAll();
  parse "../examples/proofsystems/ill";
  assert_equal true (check_atomicelim ())
;; 

let test8_at test_ctxt = 
  initAll();
  parse "../examples/proofsystems/mlj";
  assert_equal true (check_atomicelim ())
;; 

let test9_at test_ctxt = 
  initAll();
  parse "../examples/proofsystems/s4";
  assert_equal true (check_atomicelim ())
;; 

let test10_at test_ctxt = 
  initAll();
  parse "../examples/proofsystems/g3k";
  assert_equal false (check_atomicelim ())
;; 

