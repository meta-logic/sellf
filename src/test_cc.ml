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
(* parse functions  *)
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

let check_cutcoherence system_name = Coherence.cutCoherence_t system_name ;;

(* test cut coherence  *)
let test1_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/g1m";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;

let test2_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/lal";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;

let test3_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/lj";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;

let test4_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/lk";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;

let test5_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/ll";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;
(*let suite =
"suite">:::
 ["test1">:: test1_cc;
 "test2">:: test2_cc;
 "test3">:: test3_cc;
 "test4">:: test4_cc;
 "test5">:: test5_cc
  ]
;;

let () =
  run_test_tt_main suite
;;
*)


