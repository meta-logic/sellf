open ProofTree
open Subexponentials
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

let usage = "Usage: " ^ Sys.argv.(0) ^ " [-v] [-i string] [-c string]"

let argslst = [
  ("-v", Arg.Unit (fun () -> Term.verbose := true), ": set verbose on.");
  ("-i", Arg.String (fun s -> fileName := s), ": prefix of .pl and .sig file (with path)");
  ("-c", Arg.String (fun s -> check := s), ": 'principalcut', 'cutcoherence',
    'initialcoherence', 'atomicelim' or 'scopebang' (depending on what you want to check)");
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
 
let rec start () =
  initAll ();
  print_string ":> ";
    let command = "#load ../examples/proofsystems/ll" (*read_line()*) in
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
      let i = ref 0 in
      let formulas = !Specification.others @ !Specification.introRules in
      print_endline "\nThese are the formulas available: ";
      List.iter ( fun f ->
        print_endline ((string_of_int !i) ^ ". " ^ (Prints.termToString f));
        i := !i + 1
      ) formulas;
      print_newline ();
      print_endline "SELLF will generate the bipoles corresponding to the formula \
      chosen and print them in a latex file.";
      print_endline "Please type the number of the formula: ";
      let i1 = int_of_string (read_line ()) in
      print_endline "Please type the name of the file: ";
      let fileName = read_line () in
      let file = open_out (fileName^".tex") in
      let olPt = [] in
      let olPtRef = ref olPt in begin
      try match Bipole.bipole (List.nth formulas i1) with
        | bipoles ->
	  olPtRef := Derivation.transformTree bipoles;
	  List.iter (fun (olt, model) -> OlProofTree.toMacroRule olt) !olPtRef;
	  Derivation.solveFirstPhaseBpl !olPtRef;
	  Derivation.solveSndPhaseBpl !olPtRef;
          Printf.fprintf file "%s" Prints.texFileHeader;
          Printf.fprintf file "\\section{Possible bipoles for $%s$:} \n" (Prints.termToTexString (List.nth formulas i1));
          List.iter (fun (pt, model) ->
            Printf.fprintf file "%s" "{\\scriptsize";
            Printf.fprintf file "%s" "\\[";
            Printf.fprintf file "%s" (ProofTreeSchema.toTexString pt);
            Printf.fprintf file "%s" "\\]";
            Printf.fprintf file "%s" "}";
            Printf.fprintf file "%s" "CONSTRAINTS\n";
            Printf.fprintf file "%s" (Constraints.toTexString model);
          ) bipoles;   
          Printf.fprintf file "%s" "{\\section{Result:}}\n";
          List.iter (fun (olt, model) ->
            Printf.fprintf file "%s" "{\\scriptsize";
            Printf.fprintf file "%s" "\\[";
            Printf.fprintf file "%s" (OlProofTree.toTexString olt);
            Printf.fprintf file "%s" "\\]";
            Printf.fprintf file "%s" "}";
          ) !olPtRef;
          Printf.fprintf file "%s" Prints.texFileFooter;
          close_out file;

        with Bipole.Not_bipole -> print_endline "This specification is not a bipole!"
      end

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
      begin
(*      match Permutation.permute (List.nth formulas i1) (List.nth formulas i2) with
        | true -> print_endline "\nThe rules permute.\n"
        | false -> print_endline "\nThe rules do not permute.\n"*)
        let perm_bipoles = Permutation.permute (List.nth formulas i1) (List.nth formulas i2) in
        match perm_bipoles with
        | [] -> print_endline "\nThe rules do not permute.\n"
        | _ -> print_endline "Please type the name of the file: ";
	      let fileName = read_line () in
	      let file = open_out (fileName^".tex") in
	      let olPt = [] in
	      let olPtRef = ref olPt in
	      olPtRef := Derivation.transformTree' perm_bipoles;
	      List.iter (fun ((olt1, model1), (olt2, model2)) -> 
		OlProofTree.toPermutationFormat olt1;
		OlProofTree.toPermutationFormat olt2;
	      ) !olPtRef;
	      Derivation.solveFirstPhasePer !olPtRef;
	      Derivation.solveSndPhasePer !olPtRef;
	      Printf.fprintf file "%s" Prints.texFileHeader;
	      Printf.fprintf file "\\section{Possible permutations for $%s$ " (Prints.termToTexString (List.nth formulas i1));
	      Printf.fprintf file " and $%s$:} \n" (Prints.termToTexString (List.nth formulas i2));
              List.iter (fun (b12, b21) ->
		  Printf.fprintf file "%s" "{\\scriptsize";
		  Printf.fprintf file "%s" "\\[";
		  Printf.fprintf file "%s" (OlProofTree.toTexString (fst(b12)));
		  Printf.fprintf file "%s" "\\]";
		  Printf.fprintf file "%s" "}";
		  Printf.fprintf file "%s" "CONSTRAINTS\n";
		  Printf.fprintf file "%s" (Constraints.toTexString (snd(b12)));
		  Printf.fprintf file "\n \\begin{center} $\\downarrow$ \\end{center} \n";
		  Printf.fprintf file "%s" "{\\scriptsize";
		  Printf.fprintf file "%s" "\\[";
		  Printf.fprintf file "%s" (OlProofTree.toTexString (fst(b21)));
		  Printf.fprintf file "%s" "\\]";
		  Printf.fprintf file "%s" "}";
		  Printf.fprintf file "%s" "CONSTRAINTS\n";
		  Printf.fprintf file "%s" (Constraints.toTexString (snd(b21)));
              ) !olPtRef;
	      Printf.fprintf file "%s" Prints.texFileFooter;
	      close_out file;
      end

    (* Check if all rules permute *)
    (*| "#permute_all" ->
      let formulas = !Specification.others @ !Specification.introRules in
      print_endline "SELLF will check the permutation of all formulas over all \
      formulas.";
      begin
      List.iter (fun f1 -> 
        List.iter (fun f2 ->
          match Permutation.permute f1 f2 with
            | true -> ()
              (*print_endline (Prints.termToString f1);
              print_endline "\npermutes over\n";
              print_endline (Prints.termToString f2)*)
            | false -> 
              print_endline "------------------------------------------------------";
              print_endline (Prints.termToString f1);
              print_endline "\ndoes NOT permute over\n";
              print_endline (Prints.termToString f2)
        ) formulas
      ) formulas;
      print_endline "------------------------------------------------------";
      print_endline "All the other rules permute."
      end*)

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
match (!check, !fileName) with 
  | ("", "") ->
    print_endline "SELLF -- A linear logic framework for systems with locations.";
    print_endline "Version 0.5.\n";
    print_endline "Type #help for a list of available commands.\n";
    while true do
      start ()
    done
  (* Running in batch mode *)
  | ("principalcut", file) -> 
    initAll ();
    if parse file then check_principalcut ()
  | ("cutcoherence", file) -> 
    initAll ();
    if parse file then check_cutcoherence ()
  | ("initialcoherence", file) -> 
    initAll ();
    if parse file then check_initialcoherence ()
  | ("atomicelim", file) -> 
    initAll ();
    if parse file then check_atomicelim ()
  | ("scopebang", file) ->
    initAll ();
    if parse file then check_scopebang ()
  | (x, y) -> failwith ("Invalid arguments.")
;;

