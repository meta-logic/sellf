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

type systype = 
|    LL 
|    LJ 
|    MLJ 
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

let permute_bin name1 name2 = 
  let formula1 = Specification.getSpecificationOf name1 in
  let formula2 = Specification.getSpecificationOf name2 in
  match Permutation.permute formula1 formula2 with 
    (* If both lists are empty, no bipoles could be constructed. *)
    | (true, [], []) -> NA
    (* Else if there are no failures the second list should be empty. *)
    | (true, pairs, []) -> TRUE;
    (* Else, some permutation was not possible. *)
    | (false, _, bipoles) -> FALSE;
    | _ -> FALSE;
;;

(*`Test ll permutations *)
let failure () = failwith "parse unsuccessful";;

let helper (name1, name2, sys, sol) = 
	match sys with 
	  |  LL  -> let _ = initAll() in 
	  		if parse "../examples/proofsystems/ll" then (name1 ^ "->" ^ name2, (permute_bin name1 name2), sol)
	  		else failure();
	  |  LJ -> let _ = initAll() in
	  		if parse "../examples/proofsystems/lj" then (name1 ^ "->" ^ name2, (permute_bin name1 name2), sol)
	  		else failure();
	  |  MLJ -> let _ = initAll() in 
	  		if parse "../examples/proofsystems/mlj" then (name1 ^ "->" ^ name2, (permute_bin name1 name2), sol)
	  		else failure();
	  
;;

let mycase = 
	["tensor_l", "tensor_r", LL, FALSE;
	 "tensor_l", "tensor_l", LL, TRUE;
	 "tensor_l", "lolli_r", LL, TRUE;
	 "tensor_l", "lolli_l", LL, FALSE;
	 "tensor_l", "oplus_r", LL, TRUE;
	 "tensor_l", "oplus_l", LL, TRUE;
	 "tensor_l", "with_r", LL, TRUE;
	 "tensor_l", "with_l", LL, TRUE;
	 "tensor_l", "par_r", LL, TRUE;
	 "tensor_l", "par_l", LL, FALSE;
	 "tensor_l", "lbang_r", LL, FALSE;
	 "tensor_l", "lbang_l", LL, TRUE;
	 "tensor_l","lquest_r", LL, TRUE;
	 "tensor_l","lquest_l", LL, FALSE;
	 "tensor_l", "lone_r", LL, FALSE;
	 "tensor_l", "lone_l", LL, FALSE;
	 
	 (* tensor right permutes up *)
	 "tensor_r", "tensor_r", LL, TRUE;
	 "tensor_r", "tensor_l", LL, TRUE;
	 "tensor_r", "lolli_r", LL, TRUE;
	 "tensor_r", "lolli_l", LL, TRUE;
	 "tensor_r", "oplus_r", LL, TRUE;
	 "tensor_r", "oplus_l", LL, TRUE;
	 "tensor_r", "with_r", LL, TRUE;
	 "tensor_r", "with_l", LL, TRUE;
	 "tensor_r", "par_r", LL, TRUE;
	 "tensor_r", "par_l", LL, TRUE;
	 "tensor_r", "lbang_r", LL, FALSE;
	 "tensor_r", "lbang_l", LL, TRUE;
	 "tensor_r", "lquest_r", LL, TRUE;
	 "tensor_r",  "lquest_l", LL, FALSE;
	 "tensor_r", "lone_r", LL, FALSE;
	 "tensor_r",  "lone_l", LL, TRUE;
	 "tensor_r", "lone_r", LL, TRUE;
	 "tensor_r", "lone_l", LL, FALSE;

	 (* plus right permutes up *)
	 "oplus_r", "tensor_r", LL, TRUE;
	 "oplus_r", "tensor_l", LL, TRUE;
	 "oplus_r", "lolli_r", LL, TRUE;
	 "oplus_r", "lolli_l", LL, TRUE;
	 "oplus_r", "oplus_r", LL, TRUE;
	 "oplus_r", "oplus_l", LL, TRUE;
	 "oplus_r", "with_r", LL, TRUE;
	 "oplus_r", "with_l", LL, TRUE;
	 "oplus_r", "par_r", LL, TRUE;
	 "oplus_r", "par_l", LL, TRUE;
	 "oplus_r", "lbang_r", LL, FALSE;
	 "oplus_r", "lbang_l", LL, TRUE;
	 "oplus_r", "lquest_r", LL, TRUE;
	 "oplus_r", "lquest_l", LL, FALSE;
	 "oplus_r", "lone_r", LL, FALSE;
	 "oplus_r", "lone_l", LL, TRUE;
	 "oplus_r", "lbot_r", LL, TRUE;
	 "oplus_r", "lbot_l", LL, FALSE;

	 (* with right permutes up *)
	 "with_r", "tensor_r", LL, FALSE;
	 "with_r", "tensor_l", LL, TRUE;
	 "with_r", "lolli_r", LL, TRUE;
	 "with_r", "lolli_l", LL, FALSE;
	 "with_r", "oplus_r", LL, FALSE;
	 "with_r", "oplus_l", LL, TRUE;
	 "with_r", "with_r", LL, TRUE;
	 "with_r", "with_l", LL, FALSE;
	 "with_r", "par_r", LL, TRUE;
	 "with_r", "par_l", LL, FALSE;
	 "with_r", "lbang_r", LL, FALSE;
	 "with_r", "lbang_l", LL, TRUE;
	 "with_r", "lquest_r", LL, TRUE;
	 "with_r", "lquest_l", LL, FALSE;
	 "with_r", "lone_r", LL, FALSE;
	 "with_r", "lone_l", LL, TRUE;
	 "with_r", "lbot_r", LL, TRUE;
	 "with_r", "lbot_l", LL, FALSE;


	(* impl left permutes up *)
	 "imp_l", "imp_l", LJ, TRUE;
	 "imp_l", "imp_r", LJ, TRUE;
	 "imp_l", "and_l", LJ, FALSE;
	 "imp_r", "and_r", LJ, TRUE;
	 "imp_l", "or_l", LJ, TRUE;
	 "imp_l", "or_r", LJ, TRUE;

	(* impl right permutes up *)
	"imp_r", "imp_l", LJ, FALSE;
	"imp_r", "imp_r", LJ, NA;
	"imp_r", "and_l", LJ, TRUE;
	"imp_r", "and_r", LJ, NA;
	"imp_r", "or_l", LJ, TRUE;
	"imp_r", "or_r", LJ, NA;

	(* and left permutes up *)
	"and_l", "imp_l", LJ, TRUE;
	"and_l", "imp_r", LJ,TRUE;
	"and_l", "and_l", LJ, TRUE;
	"and_l", "and_r", LJ, TRUE;
	"and_l", "or_l", LJ, TRUE;
	"and_l", "or_r", LJ, TRUE;

	(* and right permutes up *)
	"and_r", "imp_l", LJ, TRUE;
	"and_r", "imp_r", LJ, NA;
	"and_r", "and_l", LJ, TRUE;
	"and_r", "and_r", LJ, NA;
	"and_r", "or_l", LJ, TRUE;
	"and_r", "or_r", LJ, NA;

	(* impl right permutes up *)
	"imp_r", "imp_l", MLJ, FALSE;
	"imp_r", "imp_r", MLJ, NA;
	"imp_l", "and_l", MLJ, TRUE;
	"imp_r", "and_r", MLJ, NA;
	"imp_r", "or_l", MLJ, TRUE;
	"imp_r", "or_r", MLJ, NA;
	"imp_l", "imp_l", MLJ, TRUE;
	"imp_r", "imp_r", MLJ, FALSE
	]
	 ;;

let permutation_case = List.map helper mycase;;

let permutation_list =
  (List.map
    (fun (arg,res,sol) ->
      let title = arg
      in
        title >::
        (fun test_ctxt ->
          assert_equal res sol))
      permutation_case);;




