open Bipole
open Context
open ProofTree
open Subexponentials
open Prints
open OlRule
open ProofTreeSchema
open Permutation

module TestUnify = 
  Unify.Make(struct
    let instantiatable = Types.LOG
    let constant_like = Types.EIG
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

let filePrefix = "proofsTex/" ;;

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
    'initialcoherence', 'atomicelim', 'scopebang', 'rulenames', 'permute', 'bipoles' or 'rules' (depending on what you want to check)");
  ("-r1", Arg.String (fun r -> rule1 := r), ": set the name of the first rule to check the permutation above the second rule.");
  ("-r2", Arg.String (fun r -> rule2 := r), ": set the name of the second rule.");
  ("-bipole", Arg.Unit (fun () -> Permutation.setShowBipole true), ": show bipole.");
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
      | Lexer.Eof -> 
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
      | Parsing.Parse_error ->  Format.printf "Syntax error while parsing .sig file%s.\n%!" (position lexbuf); false
      | Failure _ -> Format.printf "Syntax error%s.\n%!" (position lexbuf); false
    end
end ;;

(* TODO: this function should be somewhere else and olPt should not be a mutable
object. *)
(* Ask Leo about this function. [Giselle] *)
let apply_derivation bipoles = begin 
  let olPt = ref [] in
  olPt := Derivation.remakeBipoles bipoles;
  Derivation.rewriteBipoleList !olPt;
  List.iter (fun (olt, model) -> OlProofTree.toMacroRule olt) !olPt;
  !olPt
end ;;

let print_rulenames () =
  let names = Specification.getAllRulesName () in
  List.iter (fun s ->
    print_endline s
  ) names
;;

let printOLrules bipoles fileName =
  let file = open_out (filePrefix ^ fileName ^ ".tex") in
  Printf.fprintf file "%s" Prints.texFileHeader;
  List.iter (fun bipole ->
    (* Why is the result of this method a list?? *)
    let olPt = apply_derivation bipole in
    List.iter (fun (olt, model) ->
      Printf.fprintf file "%s" "{\\scriptsize";
      Printf.fprintf file "%s" "\\[";
      Printf.fprintf file "%s" (OlProofTree.toTexString olt);
      Printf.fprintf file "%s" "\\]";
      Printf.fprintf file "%s" "}";
      (*Printf.fprintf file "Constraints: %s" (Constraints.toTexString model);*)
    ) olPt;
  ) bipoles;
  Printf.fprintf file "%s" Prints.texFileFooter;
  close_out file
;;

let printBipoles bipoles fileName = 
  let file = open_out (filePrefix ^ fileName ^ ".tex") in
  Printf.fprintf file "%s" Prints.texFileHeader;
  List.iter (fun bipole ->
    Printf.fprintf file "%s" "{\\scriptsize";
    Printf.fprintf file "%s" "\\[";
    Printf.fprintf file "%s" (ProofTreeSchema.toTexString (fst(bipole)));
    Printf.fprintf file "%s" "\\]";
    Printf.fprintf file "%s" "}";
    Printf.fprintf file "%s" "CONSTRAINTS\n";
    Printf.fprintf file "%s" (Constraints.toTexString (snd(bipole)));
    (*Printf.fprintf file "Constraints: %s" (Constraints.toTexString (snd(bipole)));*)
  ) bipoles;
  Printf.fprintf file "%s" Prints.texFileFooter;
  close_out file
;;

(* Command line #bipoles *)
let bipoles_cl () =
  let formulas = !Specification.others @ !Specification.introRules in
  let bipoles = List.fold_right (fun f acc -> try (Bipole.bipole f) :: acc
    with Bipole.Not_bipole f -> Bipole.isNotBipole f; acc
  ) formulas [] in
  List.iter (fun bipole ->
    List.iter (fun (pt, model) ->
      print_endline "\\[";
      print_endline (ProofTreeSchema.toTexString (pt));
      print_endline "\\]";
      print_endline "\\[";
      print_endline "CONSTRAINTS = ";
      print_endline (Constraints.toJaxString (model));
      print_endline "\\]";
    ) bipole;
  ) bipoles
;;

(* Command line #rules *)
let rules_cl () =
  let formulas = !Specification.others @ !Specification.introRules in
  let bipoles = List.fold_right (fun f acc -> try (Bipole.bipole f) :: acc
    with Bipole.Not_bipole f -> Bipole.isNotBipole f; acc
  ) formulas [] in
  List.iter (fun bipole ->
      let olPt = apply_derivation bipole in
      List.iter (fun (olt, model) ->
        print_endline "\\[";
        print_endline (OlProofTree.toTexString olt);
        print_endline "\\]";
      ) olPt;
  ) bipoles
;;

let permutationTex f1 f2 cl = match Permutation.permute f1 f2 with
  | (true, [], []) -> 
    "Could not build a derivation with the two chosen rules.\n\n";

  | (true, pairs, []) -> 
    "The rules permute. Here are the permutations:\n" ^ 
    (Permutation.permutationsToTexString pairs cl);
  
  | (false, ok, notok) -> 
    "The rules might not permute. These are the configurations for which a \
    permutation was found:\n" ^
    (Permutation.permutationsToTexString ok cl) ^ 
    "These are the configurations for which a permutation was not found:\n" ^
    (Permutation.nonPermutationsToTexString notok cl);
  
  | _ -> failwith ("Invalid result for permutation checking.")
;;

let permute forms_lst fileName =
  let file = open_out (filePrefix ^ fileName ^ ".tex") in
  Printf.fprintf file "%s" Prints.texFileHeader;
  List.iter (fun (f1, f2) ->
    let name1 = Specification.getRuleName f1 in
    let name2 = Specification.getRuleName f2 in
    Printf.fprintf file "\\section{Permutation of $%s$ and $%s$}\n\n" name1 name2;
    Printf.fprintf file "%s" (permutationTex f1 f2 false);
  ) forms_lst;
  Printf.fprintf file "%s" Prints.texFileFooter;
  close_out file
;;

(* permute_bin: prints yes/no, without showing the derivations *)
let permute_bin name1 name2 = 
  let formula1 = Specification.getSpecificationOf name1 in
  let formula2 = Specification.getSpecificationOf name2 in
  match Permutation.permute formula1 formula2 with 
    (* If both lists are empty, no bipoles could be constructed. *)
    | (true, [], []) -> print_endline "NO (failed constructing bipoles)"
    (* Else if there are no failures the second list should be empty. *)
    | (true, pairs, []) -> print_endline "YES";
    (* Else, some permutation was not possible. *)
    | (false, _, bipoles) -> print_endline "NO (some case is not possible)";
    | _ -> failwith ("Invalid result for permutation checking.")
;;


(* Command line #permute *)
let permute_cl name1 name2 = 
  let formula1 = Specification.getSpecificationOf name1 in
  let formula2 = Specification.getSpecificationOf name2 in
  print_endline (permutationTex formula1 formula2 true)
;;

let print_formulas formulas = 
  let i = ref 0 in
  print_endline "\nThese are the formulas available: ";
  List.iter ( fun f ->
    print_endline ((string_of_int !i) ^ ". " ^ (Prints.termToString f));
    i := !i + 1
  ) formulas;
  print_newline ()
;;

let permute_to_file name1 name2 =
  let formulas = !Specification.others @ !Specification.introRules in
  let index = ref (-1) in
  let counter () = index := !index + 1; !index in
  let i1 = ref 0 in
  let i2 = ref 0 in
  List.iter(fun f -> 
    if (Specification.getRuleName f) = name1 then i1 := counter()
    else begin
      if (Specification.getRuleName f) = name2 then i2 := counter()
      else index := !index + 1;
    end
  );
  permute [((List.nth formulas !i1), (List.nth formulas !i2))] "permutation"
;;

let rules_to_file () =
  let formulas = !Specification.others @ !Specification.introRules in
  let bipoles = List.map (fun f -> Bipole.bipole f) formulas in
  printOLrules bipoles "rules"
;;

let bipoles_to_file () =
  let formulas = !Specification.others @ !Specification.introRules in
  let bipoles = List.fold_right (fun f acc -> (Bipole.bipole f) @ acc) formulas [] in
  printBipoles bipoles "bipoles"
;;
 
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

    (* Generates the bipole of a rule of the object logic and prints a latex file with it *)
    | "#bipole" -> 
      let formulas = !Specification.others @ !Specification.introRules in
      print_formulas formulas;
      print_endline "The bipoles for the chosen formula will be generated and \
      printed to a LaTeX file.\nPlease choose a formula by its number:";
      let i1 = int_of_string (read_line ()) in
      print_endline "Please choose a name for the file:";
      let f = read_line () in
      let bp = Bipole.bipole (List.nth formulas i1) in
      printBipoles bp f

    (* Generates all bipoles of all rules of the object logic and prints a latex file with them *)
    | "#bipoles" ->
      print_newline ();
      print_endline "All the bipoles of the specification will be generated \
      and printed in a latex file.\nPlease choose a name for the file:";
      let f = read_line () in
      let formulas = !Specification.others @ !Specification.introRules in
      let bipoles = List.fold_right (fun f acc -> (Bipole.bipole f) @ acc) formulas [] in
      printBipoles bipoles f

    (* Check if all rules are bipoles *)
    | "#check_rules" -> 
      let formulas = Specification.getAllRules () in
      List.iter (fun f -> match Term.isBipole f with
        | true -> ()
        | false -> print_endline ("The following formula is NOT a bipole: " ^ (Prints.termToString f))
      ) formulas

    (* Generates a rule of the object logic and prints a latex file with it *)
    | "#rule" -> 
      let formulas = !Specification.others @ !Specification.introRules in
      print_formulas formulas;
      print_endline "The object logic rule of the chosen formula will be generated and \
      printed to a LaTeX file.\nPlease choose a formula by its number:";
      let i1 = int_of_string (read_line ()) in
      print_endline "Please choose a name for the file:";
      let f = read_line () in
      let bp = Bipole.bipole (List.nth formulas i1) in
      printOLrules [bp] f

    (* Generates all rules of the object logic and prints a latex file with them *)
    | "#rules" ->
      print_newline ();
      print_endline "The object logic rules of all the formulas of the specification \
      will be generated and printed in a latex file.\nPlease choose a name for the file:";
      let f = read_line () in
      let formulas = !Specification.others @ !Specification.introRules in
      let bipoles = List.map (fun f -> Bipole.bipole f) formulas in
      printOLrules bipoles f

    (* Check if two rules permute *)
    | "#permute" -> 
      let formulas = !Specification.others @ !Specification.introRules in
      print_formulas formulas;
      print_endline "Checking the permutation of one formula F1 over \
      another F2 (i.e., can a derivation where F1 is below F2 be transformed \
      into a derivation where F2 is below F1?) \n";
      print_endline "Please type the number of F1: ";
      let i1 = int_of_string (read_line ()) in
      print_endline "Please type the number of F2: ";
      let i2 = int_of_string (read_line ()) in
      print_endline "Please type a file name for the results:";
      let f = read_line () in
      permute [((List.nth formulas i1), (List.nth formulas i2))] f

    (* Check if all rules permute *)
    | "#permute_all" ->
      let formulas = !Specification.others @ !Specification.introRules in
      print_endline "Checking the permutation of all formulas over all \
      formulas.\nPlease type a file name for the results:";
      let f = read_line () in
      let pairs = List.fold_right (fun f1 acc -> 
        List.fold_right (fun f2 acc2 ->
          (f1, f2) :: acc2 
        ) formulas acc
      ) formulas [] in
      permute pairs f

    (* Prints all sets of rules (one per line) such that all rules within one
     * set permute over each other.
     *)
    | "#permutation_cliques" ->
      print_newline ();
      print_endline "Rules belonging to the same group permute over each other.";
      print_endline "Ci < Cj iff every rule rj in Cj permutes up every rule ri in Ci, i.e., rj -> ri in G.";
      print_endline "This may take a while, please be patient...\n";
      let formulas = !Specification.others @ !Specification.introRules @ !Specification.structRules in
      let cliques = Permutation.getPermutationCliques formulas in
      let graph = Permutation.getPermutationGraph formulas in
      let pairs = Permutation.getCliquesOrdering cliques graph in
      Hashtbl.iter (fun clq name ->
        print_string (name ^ ": [ ");
        List.iter (fun v -> print_string (v ^ ", ")) clq;
        print_string " ]\n";
      ) cliques;
      print_newline ();
      List.iter (fun (c1, c2) ->
        print_endline (c1 ^ " < " ^ c2);
      ) pairs;
      print_newline ()

    (* Generates the permutation graph of all rules of the object logic and
     * prints it to a dot file *)
    | "#permutation_dot_graph" ->
      print_newline ();
      print_endline "The permutation graph of all rules of the specification \
      will be generated in the dot format and printed to a file. To see the \
      actual graph, you need to have graphviz installed and run 'dot -Tpdf \
      filename.dot -o filename.pdf'.\nPlease choose a name for the file:";
      let filename = read_line () in
      let file = open_out (filePrefix ^ filename ^ ".dot") in
      let formulas = !Specification.others @ !Specification.introRules in
      Printf.fprintf file "%s" (Permutation.getPermutationDotGraph formulas);
      close_out file

    | "#permutation_table" ->
      print_newline ();
      print_endline "The permutation table of all rules of the specification \
      will be generated in the tex format and printed to a file.\nPlease choose \
      a name for the file:";
      let filename = read_line () in
      let file = open_out (filePrefix ^ filename ^ ".tex") in
      let formulas = !Specification.others @ !Specification.introRules in
      Printf.fprintf file "%s" (Permutation.getPermutationTable formulas);

    | "#cutcoherence" -> check_cutcoherence ()
    
    | "#initialcoherence" -> check_initialcoherence ()

    | "#scopebang" -> check_scopebang ()

    | "#atomicelim" -> check_atomicelim () 

    | "#principalcut" -> check_principalcut ()

    (* Query *)
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
  (* Load file from the command line *)
  | ("", file, _, _) ->
    initAll();
    if parse file then begin
      print_endline "SELLF -- A linear logic framework for systems with locations.";
      print_endline "Version 0.5.\n";
      print_endline ("The file: " ^ file ^ " was loaded.\n");
      while true do
        solve_query ()
      done
    end
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
  | ("bipoles", file, _, _) ->
    initAll ();
    if parse file then bipoles_cl ()
  | ("rules", file, _, _) ->
    initAll ();
    if parse file then rules_cl ()
  | ("permute", file, r1, r2) ->
    initAll ();
    if parse file then permute_cl r1 r2
  | ("rulenames", file, _, _) ->
    initAll ();
    if parse file then print_rulenames ()
  | ("permutebin", file, r1, r2) ->
    initAll ();
    if parse file then permute_bin r1 r2
  | ("bipoles_to_file", file, _, _) ->
    initAll ();
    if parse file then bipoles_to_file ()
  | ("rules_to_file", file, _, _) ->
    initAll ();
    if parse file then rules_to_file ()
  | ("permute_to_file", file, r1, r2) ->
    initAll ();
    if parse file then permute_to_file r1 r2
  | (x, y, _, _) -> failwith ("Invalid arguments.")
;;

