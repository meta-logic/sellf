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

let parse file_name =
  let file_sig = open_in (file_name^".sig") in
  let lexbuf = Lexing.from_channel file_sig in
  try
    let (kt, tt) = Parser.signature Lexer.token lexbuf in
      Specification.initialize ();
      (* Copying one table into another. This is a hack that will be removed
      once specification.ml is transformed into a proper module. *)
      Hashtbl.iter (fun _ v -> let _ = Specification.addKindTbl v in ()) kt;
      Hashtbl.iter (fun k v -> Specification.addTypeTbl k v) tt;
      let file_prog = open_in (file_name^".pl") in 
      let lexbuf = Lexing.from_channel file_prog in
      try
        let (s, c, i, a) = Parser.specification Lexer.token lexbuf in
          (* Hack to be removed once specification.ml is a proper module *)
          Specification.structRules := List.rev s;
          Specification.cutRules := List.rev c;
          Specification.introRules := List.rev i;
          Specification.axioms := List.rev a; true
      with
      | Parsing.Parse_error ->  Format.printf "Syntax error while parsing .pl file%s.\n%!" (position lexbuf); false
      | Failure str -> Format.printf ("ERROR:%s\n%!") (position lexbuf); print_endline str; false
  with
  | Parsing.Parse_error ->  Format.printf "Syntax error while parsing .sig file%s.\n%!" (position lexbuf); false
  | Failure _ -> Format.printf "Syntax error%s.\n%!" (position lexbuf); false
;;

let check_principalcut () = begin
  if Staticpermutationcheck.cut_principal () then true
     else false
end ;;

(* Test principalcut *)
let test1_pc test_ctxt = 
  initAll();
  parse "../examples/proofsystems/g1m";
  assert_equal true (check_principalcut ())
;;

let test2_pc test_ctxt = 
  initAll();
  parse "../examples/proofsystems/lal";
  assert_equal true (check_principalcut ())
;; 

let test3_pc test_ctxt = 
  initAll();
  parse "../examples/proofsystems/lax";
  assert_equal true (check_principalcut ())
;; 

let test4_pc test_ctxt = 
  initAll();
  parse "../examples/proofsystems/lj";
  assert_equal true (check_principalcut ())
;; 

let test5_pc test_ctxt = 
  initAll();
  parse "../examples/proofsystems/lk";
  assert_equal true (check_principalcut ())
;; 

let test6_pc test_ctxt = 
  initAll();
  parse "../examples/proofsystems/ll";
  assert_equal true (check_principalcut ())
;; 

let test7_pc test_ctxt = 
  initAll();
  parse "../examples/proofsystems/ill";
  assert_equal false (check_principalcut ())
;; 

let test8_pc test_ctxt = 
  initAll();
  parse "../examples/proofsystems/mlj";
  assert_equal false (check_principalcut ())
;; 

let test9_pc test_ctxt = 
  initAll();
  parse "../examples/proofsystems/s4";
  assert_equal false (check_principalcut ())
;; 

let test10_pc test_ctxt = 
  initAll();
  parse "../examples/proofsystems/g3k";
  assert_equal false (check_principalcut ())
;; 
