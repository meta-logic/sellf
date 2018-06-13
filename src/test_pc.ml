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


let check_principalcut () = begin
  if Staticpermutationcheck.cut_principal () then true
     else false
end ;;

let fail () = failwith "parse unsuccessful";;
(*	Test principalcut *)
let test1_pc test_ctxt = 
	initAll();
 	if parse "../examples/proofsystems/g1m"
  then assert_equal true (check_principalcut ())
  else fail();;


let test2_pc test_ctxt = 
	initAll();
 	if parse "../examples/proofsystems/lal"
  then assert_equal true (check_principalcut ())
  else fail();; 

let test3_pc test_ctxt = 
	initAll();
 	if parse "../examples/proofsystems/lax"
  then assert_equal true (check_principalcut ())
  else fail();; 

let test4_pc test_ctxt = 
	initAll();
 	if parse "../examples/proofsystems/lj"
  then assert_equal true (check_principalcut ())
  else fail();; 

let test5_pc test_ctxt = 
	initAll();
 	if parse "../examples/proofsystems/lk"
  then assert_equal true (check_principalcut ())
  else fail();; 

let test6_pc test_ctxt = 
	initAll();
 	if parse "../examples/proofsystems/ll"
  then assert_equal true (check_principalcut ())
  else fail();; 

let test7_pc test_ctxt = 
	initAll();
 	if parse "../examples/proofsystems/ill"
  then assert_equal false (check_principalcut ())
  else fail();; 

let test8_pc test_ctxt = 
	initAll();
 	if parse "../examples/proofsystems/mlj"
  then assert_equal false (check_principalcut ())
  else fail();; 

let test9_pc test_ctxt = 
	initAll();
 	if parse "../examples/proofsystems/s4"
  then assert_equal false (check_principalcut ())
  else fail();; 

let test10_pc test_ctxt = 
	initAll();
 	if parse "../examples/proofsystems/g3k";
  then assert_equal false (check_principalcut ())
  else fail();; 