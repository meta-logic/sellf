open ProofTree
open Subexponentials
open Prints
open Ol

module TestUnify = 
  Unify.Make(struct
    let instantiatable = Term.LOG
    let constant_like = Term.EIG
  end)

let position lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let file = curr.Lexing.pos_fname in
  let line = curr.Lexing.pos_lnum in
  let char = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    if file = "" then
      () (* lexbuf information is rarely accurate at the toplevel *)
    else
      print_string "";Format.sprintf ": line %d, character %d" line char

let samefile = ref true ;;
let fileName = ref "" ;;
let check = ref "" ;;
let rule1 = ref "" ;;
let rule2 = ref "" ;;

let usage = "Usage: " ^ Sys.argv.(0) ^ " [-v] [-i string] [-c string]"

let argslst = [
  ("-v", Arg.Unit (fun () -> Term.verbose := true), ": set verbose on.");
  ("-i", Arg.String (fun s -> fileName := s), ": prefix of .pl and .sig file (with path)");
  ("-c", Arg.String (fun s -> check := s), ": 'principalcut', 'cutcoherence',
    'initialcoherence', 'atomicelim', 'scopebang', 'rulenames', 'permute' or 'bipole' (depending on what you want to check)");
  ("-r1", Arg.String (fun r -> rule1 := r), ": set the name of the first rule to check the permutation above the second rule.");
  ("-r2", Arg.String (fun r -> rule2 := r), ": set the name of the second rule.");
]

let initAll () = 
  Specification.initialize ();
  Context.initialize ();
  Subexponentials.initialize ();
  Coherence.initialize ();
;;

let check_principalcut () = begin
  if Staticpermutationcheck.cut_principal () then 
    print_endline "Tatu could infer that reduction to principal cuts is possible." else
    print_endline "\nCould not reduce to principal cuts.
      \nObservation: It is very likely that the cases shown above are valid permutations by vacuosly."
end ;;

let check_atomicelim () = begin
  if Staticpermutationcheck.weak_coherent () then 
  print_endline "Tatu could infer that it is always possible to eliminate atomic cuts." else
  print_endline "\nCould not infer how to eliminate atomic cuts."  
end ;;

let check_cutcoherence () = Coherence.cutCoherence () ;;
let check_initialcoherence () = Coherence.initialCoherence () ;;

let check_scopebang () = begin
  print_endline "Please type the subexponential:";
  let s = read_line() in
  let ers = Subexponentials.erased_bang s in
  let ept = Subexponentials.empty_bang s in
  print_endline ("!"^s^"  : ");
  print_endline "The following will have their formulas erased: ";
  List.iter (fun a -> print_string (a^", ")) ers; print_newline ();
  print_endline "The following should be empty: ";
  List.iter (fun a -> print_string (a^", ")) ept; print_newline ();
end ;;

let parse file_name = begin
  let file_sig = open_in (file_name^".sig") in
  let lexbuf = Lexing.from_channel file_sig in
  begin
    try 
      while true do
        let _ = Parser.types Lexer.token lexbuf in ();
      done; true
    with 
      |  Lexer.Eof -> 
          let file_prog = open_in (file_name^".pl") in 
          let lexbuf = Lexing.from_channel file_prog in
            begin
            try
              while true do
                let _ = Parser.clause Lexer.token lexbuf in ();
              done; true 
            with
              | Lexer.Eof -> true
              | Parsing.Parse_error ->  Format.printf "Syntax error while parsing .pl file%s.\n%!" (position lexbuf); false
              | Failure str -> Format.printf ("ERROR:%s\n%!") (position lexbuf); print_endline str; false
            end
      |  Parsing.Parse_error ->  Format.printf "Syntax error while parsing .sig file%s.\n%!" (position lexbuf); false
      |  Failure _ -> Format.printf "Syntax error%s.\n%!" (position lexbuf); false
    end
end ;;

let get_bipoles () = begin
  let formulas = !Specification.others @ !Specification.introRules in
  let bpl_lst = ref [] in
  let all_bipoles = List.for_all (fun f -> 
    try match Bipole.bipole f with
    | bipole -> bpl_lst := !bpl_lst @ [bipole]; 
    true
    with Bipole.Not_bipole -> false    
  ) formulas in (all_bipoles, !bpl_lst)
end ;;

let apply_derivation bipoles = begin 
  let olPt = ref [] in
  olPt := Derivation.transformTree bipoles;
  List.iter (fun (olt, model) -> OlProofTree.toMacroRule olt) !olPt;
  Derivation.solveFirstPhaseBpl !olPt;
  Derivation.solveSndPhaseBpl !olPt;
  !olPt
end ;;

let get_form_index n rules_lst = begin
  let i = ref 0 in
  let count = ref true in
  List.iter (fun (rule, side) -> 
    let finalRule = (rule ^ "_" ^ side) in
    if n = finalRule then count := false
    else begin
      if !count then i := !i + 1
      else () 
    end
  ) rules_lst;
  !i
end ;;

let get_rulenames () = begin
  let formulas = !Specification.others @ !Specification.introRules in
  let rules_lst = List.map (fun f ->
    let rule = termToTexString (OlSequent.getOnlyRule (OlSequent.formatForm (f))) in
    let side = OlContext.getFormSide f in (rule, side)
  ) formulas in rules_lst
end ;;  

let print_rulenames () = begin
  let rules_lst = get_rulenames () in
  List.iter (fun (rule, side) ->
    print_endline (rule ^ "_" ^ side);
  ) rules_lst
end ;;

let bipole () = 
  print_endline "Please type the name of the file: ";
  let olPt = ref [] in
  let fileName = read_line () in
  let file = open_out (fileName^".tex") in
  let pair_bpl = get_bipoles () in
  let all_bipoles = fst(pair_bpl) in
  let bpl_lst = snd(pair_bpl) in
  if all_bipoles then begin
    Printf.fprintf file "%s" Prints.texFileHeader;
    List.iter (fun bipoles ->
      olPt := apply_derivation bipoles;
      List.iter (fun (olt, model) ->
				Printf.fprintf file "%s" "{\\scriptsize";
				Printf.fprintf file "%s" "\\[";
				Printf.fprintf file "%s" (OlProofTree.toTexString olt);
				Printf.fprintf file "%s" "\\]";
				Printf.fprintf file "%s" "}";
      ) !olPt;
    ) bpl_lst;
    Printf.fprintf file "%s" Prints.texFileFooter;
    close_out file;
    end
  else print_endline "This specification is not a bipole!";;
  
(* Command line #bipole *)
let bipole_cl () = begin
  let olPt = ref [] in
  let pair_bpl = get_bipoles () in
  let all_bipoles = fst(pair_bpl) in
  let bpl_lst = snd(pair_bpl) in begin
  if all_bipoles then
  List.iter (fun bipoles ->
    olPt := apply_derivation bipoles;
    List.iter (fun (olt, model) ->
      print_endline "\\[";
      print_endline (OlProofTree.toTexString olt);
      print_endline "\\]";
    ) !olPt;
  ) bpl_lst
  else print_endline "This specification is not a bipole!"
  end
end;;
  
let permute formulas i1 i2 =
  let perm_pair = Permutation.permute (List.nth formulas i1) (List.nth formulas i2) in
  let perm_bipoles = fst(perm_pair) in
  let perm_not_found = snd(perm_pair) in
  match perm_bipoles with
  | [] -> begin match perm_not_found with
    | [] -> print_endline "\nThe rules do not permute.\nThe first rule do not have premises, hence is not possible to show the derivation."
    | _ -> print_endline "\nThe rules do not permute.\nPlease type the name of the file to print the derivation that can not be permuted : ";
    let fileName = read_line () in
    let file = open_out (fileName^".tex") in
    let olPt = apply_perm_not_found perm_not_found in
    Printf.fprintf file "%s" Prints.texFileHeader;
    List.iter (fun (olt, model) ->
      OlProofTree.toPermutationFormat olt;
      Printf.fprintf file "%s" "{\\scriptsize";
      Printf.fprintf file "%s" "\\[";
      Printf.fprintf file "%s" (OlProofTree.toTexString olt);
      Printf.fprintf file "%s" "\\]";
      Printf.fprintf file "%s" "}";
    ) olPt;
    Printf.fprintf file "%s" Prints.texFileFooter;
    close_out file;
    end
  | _ -> print_endline "\nThe rules permute.\nPlease type the name of the file to print the permutations: ";
    let fileName = read_line () in
    Permutation.printPermutations fileName perm_bipoles
;;


(* Command line #permute *)
let permute_cl n1 n2 = begin
  let formulas = !Specification.others @ !Specification.introRules in
  let rulesList = get_rulenames () in
  let rules_length = List.length rulesList in
  let i1 = get_form_index n1 rulesList in
  let i2 = get_form_index n2 rulesList in 
  let perm_pair = Permutation.permute (List.nth formulas i1) (List.nth formulas i2) in
  let perm_bipoles = fst(perm_pair) in
  let perm_not_found = snd(perm_pair) in
    match perm_bipoles with
    | [] -> begin match perm_not_found with
      | [] -> print_endline "\nThe rules do not permute.\nThe first rule do not have premises, hence is not possible to show the derivation."
      | _ -> print_endline "\nThe rules do not permute.\nThe derivation that can not be permuted are shown below: ";
      let olPt = apply_perm_not_found perm_not_found in
      List.iter (fun (olt, model) ->
				OlProofTree.toPermutationFormat olt;
				print_endline "\\[";
				print_endline (OlProofTree.toTexString olt);
				print_endline "\\]";
      ) olPt 
      end
    | _ -> print_endline "\nThe rules permute.\nThe permutations are shown below: ";
      let olPt = apply_permute perm_bipoles in
      List.iter (fun (b12, b21) ->
		    print_endline "\\[";
		    print_endline (OlProofTree.toTexString (fst(b12)));
			  print_endline "\n\\quad\\rightsquigarrow\\quad\n";
			  print_endline (OlProofTree.toTexString (fst(b21)));
			  print_endline "\\]";
      ) olPt
      end;;
 
let rec start () =
  initAll ();
  print_string ":> ";
    let command = read_line() in
    try 
      let lexbuf_top = Lexing.from_string command in 
      let action = Parser.top Lexer_top.token lexbuf_top in 
      match action with
      | "help" -> start ()
      | "verbose-on" -> print_endline "Verbose is set to on."; Term.verbose := true; start ()
      | "verbose-off" -> print_endline "Verbose is set to off."; Term.verbose := false; start ()
      | "time-on" -> Term.time := true; print_endline "Time is set to on."; start ()
      | "time-off" -> Term.time := false; print_endline "Time is set to off."; start ()
      | file_name -> 
        print_endline ("Loading file "^file_name);
        if parse file_name then begin
          samefile := true;
          while !samefile do 
            solve_query (); 
          done
        end
        else start ();
    with
    |  Parsing.Parse_error ->  print_endline "Invalid command. For more information type #help."; start  ()
    |  Sys_error str -> print_string ("Error"^str); print_endline ". Please double check the name of the file."; start ()
and
solve_query () = 
  print_string "?> ";
  let query_string = read_line() in
  if query_string = "#done" then samefile := false      
  else begin
  match query_string with 

    (* Check if all rules are bipoles *)
    | "#check_rules" -> 
      let formulas = Specification.getAllRules () in
      List.iter (fun f -> match Term.isBipole f with
        | true -> ()
        | false -> print_endline ("The following formula is NOT a bipole: " ^ (Prints.termToString f))
      ) formulas

    (* Generates the bipole of a rule and prints a latex file with it *)
    | "#bipole" ->
      print_newline ();
      print_endline "SELLF will generate all the bipoles of the especification and print them in a latex file.";
      bipole ()

    (* Check if two rules permute *)
    | "#permute" -> 
      let i = ref 0 in
      let formulas = !Specification.others @ !Specification.introRules in
      print_endline "\nThese are the formulas available: ";
      List.iter ( fun f ->
        print_endline ((string_of_int !i) ^ ". " ^ (Prints.termToString f));
        i := !i + 1
      ) formulas;
      print_newline ();
      print_endline "SELLF will check the permutation of one formula F1 over \
      another F2 (i.e., can a derivation where F1 is below F2 be transformed \
      into a derivation where F2 is below F1?) \n";
      print_endline "Please type the number of F1: ";
      let i1 = int_of_string (read_line ()) in
      print_endline "Please type the number of F2: ";
      let i2 = int_of_string (read_line ()) in
      permute formulas i1 i2

    (* Check if all rules permute *)
    | "#permute_all" ->
      let formulas = !Specification.others @ !Specification.introRules in
      print_endline "SELLF will check the permutation of all formulas over all \
      formulas.";
      begin
      let permutations = List.fold_right (fun f1 acc -> 
        List.fold_right (fun f2 acc2 ->
          match Permutation.permute f1 f2 with
            | ([], _) -> 
              print_endline (Prints.termToString f1);
              print_endline "\ndoes NOT permute over\n";
              print_endline (Prints.termToString f2);
              acc2
            | (perm_bipoles, _) -> perm_bipoles @ acc2
        ) formulas acc
      ) formulas [] in
      print_endline("Please type the name of the file to print the permutations:");
      let fileName = read_line() in
        Permutation.printPermutations fileName permutations
      end

    | "#cutcoherence" -> check_cutcoherence ()
    
    | "#initialcoherence" -> check_initialcoherence ()

    | "#scopebang" -> check_scopebang ()

    | "#atomicelim" -> check_atomicelim () 

    | "#principalcut" -> check_principalcut ()

    | _ -> begin
      let query = Lexing.from_string query_string in
      begin
      try 
        let _ = Parser.goal Lexer.token query in 
          begin
            Context.createProofSearchContext ();
            Boundedproofsearch.prove !Term.goal !Term.psBound (fun () ->
              print_string "\nYes.\n";
            ) (fun () -> print_string "\nNo.\n")
          end
      with
        | Parsing.Parse_error -> Format.printf "Syntax error%s.\n%!" (position query); solve_query ()
        | Failure str -> Format.printf "ERROR:%s\n%!" (position query); print_endline str; start()
      end      
    end

    (*| _ -> print_endline "Function not implemented. Try again or type #done
     * and #help."*)

  end

let _ = 
Arg.parse argslst (fun x -> raise (Arg.Bad ("Bad argument: "^x))) usage;
match (!check, !fileName, !rule1, !rule2) with 
  | ("", "", _, _) ->
    print_endline "SELLF -- A linear logic framework for systems with locations.";
    print_endline "Version 0.5.\n";
    print_endline "Type #help for a list of available commands.\n";
    while true do
      start ()
    done
  (* Running in batch mode *)
  | ("principalcut", file, _, _) -> 
    initAll ();
    if parse file then check_principalcut ()
  | ("cutcoherence", file, _, _) -> 
    initAll ();
    if parse file then check_cutcoherence ()
  | ("initialcoherence", file, _, _) -> 
    initAll ();
    if parse file then check_initialcoherence ()
  | ("atomicelim", file, _, _) -> 
    initAll ();
    if parse file then check_atomicelim ()
  | ("scopebang", file, _, _) ->
    initAll ();
    if parse file then check_scopebang ()
  | ("bipole", file, _, _) ->
    initAll ();
    if parse file then bipole_cl ()
  | ("permute", file, r1, r2) ->
    initAll ();
    if parse file then permute_cl r1 r2
  | ("rulenames", file, _, _) ->
    initAll ();
    if parse file then print_rulenames ()
  | (x, y, _, _) -> failwith ("Invalid arguments.")
;;

