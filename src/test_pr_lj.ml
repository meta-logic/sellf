open OUnit2
open Bipole
open Context
open ProofTree
open Subexponentials
open Prints
open OlRule
open ProofTreeSchema
open Permutation

type boolean = 
| TRUE
| FALSE 
| NA
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



let permute_bin name1 name2 = 
  let formula1 = Specification.getSpecificationOf name1 in
  let formula2 = Specification.getSpecificationOf name2 in
  match Permutation.permute formula1 formula2 with 
    (* If both lists are empty, no bipoles could be constructed. *)
    | (true, [], []) -> NA;
    (* Else if there are no failures the second list should be empty. *)
    | (true, pairs, []) -> TRUE;
    (* Else, some permutation was not possible. *)
    | (false, _, bipoles) -> FALSE;
    | _ -> FALSE;
;;



let test_pr_lj test_cxtx = 
  initAll();
  let sameFile = parse "../examples/proofsystems/ll";
  in 
    (* tensor left permutes up*)

    assert_bool "tensor_l -> tensor_r" (permute_bin "tensor_l" "tensor_r" = FALSE);
    assert_bool "tensor_l -> tensor_l" (permute_bin "tensor_l" "tensor_l" = TRUE);

    assert_bool "tensor_l -> lolli_r" (permute_bin "tensor_l" "lolli_r" = TRUE);
    assert_bool "tensor_l -> lolli_l" (permute_bin "tensor_l" "lolli_l" = FALSE);

    assert_bool "tensor_l -> oplus_r" (permute_bin "tensor_l" "oplus_r" = TRUE);
    assert_bool "tensor_l -> oplus_l" (permute_bin "tensor_l" "oplus_l" = TRUE);

    assert_bool "tensor_l -> with_r" (permute_bin "tensor_l" "with_r" = TRUE);
    assert_bool "tensor_l -> with_l" (permute_bin "tensor_l" "with_l" = TRUE);

    assert_bool "tensor_l -> par_r" (permute_bin "tensor_l" "par_r" = TRUE);
    assert_bool "tensor_l -> par_l" (permute_bin "tensor_l" "par_l" = FALSE);

    assert_bool "tensor_l -> lbang_r" (permute_bin "tensor_l" "lbang_r" = FALSE);
    assert_bool "tensor_l -> lbang_l" (permute_bin "tensor_l" "lbang_l" = TRUE);

    assert_bool "tensor_l -> lquest_r" (permute_bin "tensor_l" "lquest_r" = TRUE);
    assert_bool "tensor_l -> lquest_l" (permute_bin "tensor_l" "lquest_l" = FALSE);

    assert_bool "tensor_l -> lone_r" (permute_bin "tensor_l" "lone_r" = FALSE);
    assert_bool "tensor_l -> lone_l" (permute_bin "tensor_l" "lone_l" = TRUE);

    assert_bool "tensor_l -> lbot_r" (permute_bin "tensor_l" "lone_r" = TRUE);
    assert_bool "tensor_l -> lbot_l" (permute_bin "tensor_l" "lone_l" = FALSE);


    (* tensor right permutes up *)

    assert_bool "tensor_r -> tenor_r" (permute_bin "tensor_r" "tensor_r" = TRUE);
    assert_bool "tensor_r -> tensor_l" (permute_bin "tensor_r" "tensor_l" = TRUE);

    assert_bool "tensor_r -> lolli_r" (permute_bin "tensor_r" "lolli_r" = TRUE);
    assert_bool "tensor_r -> lolli_l" (permute_bin "tensor_r" "lolli_l" = TRUE);

    assert_bool "tensor_r -> oplus_r" (permute_bin "tensor_r" "oplus_r" = TRUE);
    assert_bool "tensor_r -> oplus_l" (permute_bin "tensor_r" "oplus_l" = TRUE);

    assert_bool "tensor_r -> with_r" (permute_bin "tensor_r" "with_r" = TRUE);
    assert_bool "tensor_r -> with_l" (permute_bin "tensor_r" "with_l" = TRUE);

    assert_bool "tensor_r -> par_r" (permute_bin "tensor_r" "par_r" = TRUE);
    assert_bool "tensor_r -> par_l" (permute_bin "tensor_r" "par_l" = TRUE);

    assert_bool "tensor_r -> lbang_r" (permute_bin "tensor_r" "lbang_r" = FALSE);
    assert_bool "tensor_r -> lbang_l" (permute_bin "tensor_r" "lbang_l" = TRUE);

    assert_bool "tensor_r -> lquest_r" (permute_bin "tensor_r" "lquest_r" = TRUE);
    assert_bool "tensor_r -> lquest_l" (permute_bin "tensor_r" "lquest_l" = FALSE);

    assert_bool "tensor_r -> lone_r" (permute_bin "tensor_r" "lone_r" = FALSE);
    assert_bool "tensor_r -> lone_l" (permute_bin "tensor_r" "lone_l" = TRUE);

    assert_bool "tensor_r -> lbot_r" (permute_bin "tensor_r" "lone_r" = TRUE);
    assert_bool "tensor_r -> lbot_l" (permute_bin "tensor_r" "lone_l" = FALSE);

    (* plus right permutes up *)

    assert_bool "oplus_r -> tenor_r" (permute_bin "oplus_r" "tensor_r" = TRUE);
    assert_bool "oplus_r -> tensor_l" (permute_bin "oplus_r" "tensor_l" = TRUE);

    assert_bool "oplus_r -> lolli_r" (permute_bin "oplus_r" "lolli_r" = TRUE);
    assert_bool "oplus_r -> lolli_l" (permute_bin "oplus_r" "lolli_l" = TRUE);

    assert_bool "oplus_r -> oplus_r" (permute_bin "oplus_r" "oplus_r" = TRUE);
    assert_bool "oplus_r -> oplus_l" (permute_bin "oplus_r" "oplus_l" = TRUE);

    assert_bool "oplus_r -> with_r" (permute_bin "oplus_r" "with_r" = TRUE);
    assert_bool "oplus_r -> with_l" (permute_bin "oplus_r" "with_l" = TRUE);

    assert_bool "oplus_r -> par_r" (permute_bin "oplus_r" "par_r" = TRUE);
    assert_bool "oplus_r -> par_l" (permute_bin "oplus_r" "par_l" = TRUE);

    assert_bool "oplus_r -> lbang_r" (permute_bin "oplus_r" "lbang_r" = FALSE);
    assert_bool "oplus_r -> lbang_l" (permute_bin "oplus_r" "lbang_l" = TRUE);

    assert_bool "oplus_r -> lquest_r" (permute_bin "oplus_r" "lquest_r" = TRUE);
    assert_bool "oplus_r -> lquest_l" (permute_bin "oplus_r" "lquest_l" = FALSE);

    assert_bool "oplus_r -> lone_r" (permute_bin "oplus_r" "lone_r" = FALSE);
    assert_bool "oplus_r -> lone_l" (permute_bin "oplus_r" "lone_l" = TRUE);

    assert_bool "oplus_r -> lbot_r" (permute_bin "oplus_r" "lone_r" = TRUE);
    assert_bool "oplus_r -> lbot_l" (permute_bin "oplus_r" "lone_l" = FALSE);

     (* with right permutes up *)

    assert_bool "with_r -> tenor_r" (permute_bin "with_r" "tensor_r" = FALSE);
    assert_bool "with_r -> tensor_l" (permute_bin "with_r" "tensor_l" = TRUE);

    assert_bool "with_r -> lolli_r" (permute_bin "with_r" "lolli_r" = TRUE);
    assert_bool "with_r -> lolli_l" (permute_bin "with_r" "lolli_l" = FALSE);

    assert_bool "with_r -> oplus_r" (permute_bin "with_r" "oplus_r" = FALSE);
    assert_bool "with_r -> oplus_l" (permute_bin "with_r" "oplus_l" = TRUE);

    assert_bool "with_r -> with_r" (permute_bin "with_r" "with_r" = TRUE);
    assert_bool "with_r -> with_l" (permute_bin "with_r" "with_l" = FALSE);

    assert_bool "with_r -> par_r" (permute_bin "with_r" "par_r" = TRUE);
    assert_bool "with_r -> par_l" (permute_bin "with_r" "par_l" = FALSE);

    assert_bool "with_r -> lbang_r" (permute_bin "with_r" "lbang_r" = FALSE);
    assert_bool "with_r -> lbang_l" (permute_bin "with_r" "lbang_l" = TRUE);

    assert_bool "with_r -> lquest_r" (permute_bin "with_r" "lquest_r" = TRUE);
    assert_bool "with_r -> lquest_l" (permute_bin "with_r" "lquest_l" = FALSE);

    assert_bool "with_r -> lone_r" (permute_bin "with_r" "lone_r" = FALSE);
    assert_bool "with_r -> lone_l" (permute_bin "with_r" "lone_l" = TRUE);

    assert_bool "with_r -> lbot_r" (permute_bin "oplus_r" "lone_r" = TRUE);
    assert_bool "with_r -> lbot_l" (permute_bin "oplus_r" "lone_l" = FALSE);

  initAll();
  let sameFile = parse "../examples/proofsystems/lj" 
  in

  (* impl left permutes up *)
  assert_bool "imp_l -> imp_l" (permute_bin "imp_l" "imp_l" = TRUE);
  assert_bool "imp_l -> imp_r" (permute_bin "imp_r" "imp_r" = TRUE);

  assert_bool "imp_l -> and_l" (permute_bin "imp_l" "and_l" = FALSE);
  assert_bool "imp_l -> and_r" (permute_bin "imp_r" "and_r" = TRUE);

  assert_bool "imp_l -> or_l" (permute_bin "imp_l" "or_l" = TRUE);
  assert_bool "imp_l -> or_r" (permute_bin "imp_r" "or_r" = TRUE);

  (* impl right permutes up *)
  assert_bool "imp_r -> imp_l" (permute_bin "imp_r" "imp_l" = TRUE);
  assert_bool "imp_r -> imp_r" (permute_bin "imp_r" "imp_r" = NA);

  assert_bool "imp_r -> and_l" (permute_bin "imp_r" "and_l" = TRUE);
  assert_bool "imp_r -> and_r" (permute_bin "imp_r" "and_r" = NA);

  assert_bool "imp_r -> or_l" (permute_bin "imp_r" "or_l" = TRUE);
  assert_bool "imp_r -> or_r" (permute_bin "imp_r" "or_r" = NA);

  (* and left permutes up *)
  assert_bool "and_l ->imp_l" (permute_bin "and_l" "imp_l" = TRUE);
  assert_bool "and_l -> imp_r" (permute_bin "and_l" "imp_r" = TRUE);

  assert_bool "and_l -> and_l" (permute_bin "and_l" "and_l" = TRUE);
  assert_bool "and_l -> and_r" (permute_bin "and_l" "and_r" = TRUE);

  assert_bool "and_l -> or_l" (permute_bin "and_l" "or_l" = TRUE);
  assert_bool "and_l -> or_r" (permute_bin "and_l" "or_r" = TRUE);

  (* and right permutes up *)
  assert_bool "and_r ->imp_l" (permute_bin "and_r" "imp_l" = TRUE);
  assert_bool "and_r -> imp_r" (permute_bin "and_r" "imp_r" = NA);

  assert_bool "and_r -> and_l" (permute_bin "and_l" "and_l" = TRUE);
  assert_bool "and_r -> and_r" (permute_bin "and_l" "and_r" = NA);

  assert_bool "and_r -> or_l" (permute_bin "and_l" "or_l" = TRUE);
  assert_bool "and_r -> or_r" (permute_bin "and_l" "or_r" = NA);

  let sameFile = parse "../examples/proofsystems/mlj"
  in 
  (* impl right permutes up *)
  assert_bool "imp_r -> imp_l" (permute_bin "imp_r" "imp_l" = FALSE);
  assert_bool "imp_r -> imp_r" (permute_bin "imp_r" "imp_r" = NA);

  assert_bool "imp_r -> and_l" (permute_bin "imp_l" "and_l" = TRUE);
  assert_bool "imp_r -> and_r" (permute_bin "imp_r" "and_r" = NA);

  assert_bool "imp_r -> or_l" (permute_bin "imp_r" "or_l" = TRUE);
  assert_bool "imp_r -> or_r" (permute_bin "imp_r" "or_r" = NA);

  (*impl left permutes up *)
  assert_bool "imp_l -> imp_l" (permute_bin "imp_l" "imp_l" = TRUE);
  assert_bool "imp_l -> imp_r" (permute_bin "imp_r" "imp_r" = FALSE);;