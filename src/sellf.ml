open Bipole
open Context
open ProofTree
open Subexponentials
open Specification
open Prints
open OlRule
open ProofTreeSchema
open Permutation
open TypeChecker

module TestUnify = 
  Unify.Make(struct
    let instantiatable = Types.LOG
    let constant_like = Types.EIG
  end)

let samefile = ref true ;;

let initAll () = 
  Context.initialize ();
  Subexponentials.initialize ();
;;

let fn = ref "" ;;

let check_principalcut spec =
  if Staticpermutationcheck.cut_principal spec then 
    print_endline "Tatu could infer that reduction to principal cuts is possible." 
  else
    print_endline "\nCould not reduce to principal cuts.
      \nObservation: It is very likely that the cases shown above are valid permutations by vacuosly."
;;

let check_atomicelim spec =
  if Staticpermutationcheck.weak_coherent spec then 
    print_endline "Tatu could infer that it is always possible to eliminate atomic cuts." 
  else
    print_endline "\nCould not infer how to eliminate atomic cuts."  
;;

let check_cutcoherence system_name spec = 
  let coherent = Hashtbl.fold (fun conn specs res -> 
    let d = Coherence.checkDuality system_name conn specs spec
    in
    if d then print_string ("====> Connective "^conn^" has dual specification.\n")
    else print_string ("x ==> Connective "^conn^" does not have dual specifications.\n") ;
    d && res 
  ) (Specification.getLRHash spec) true
  in
  if coherent then print_string "\nTatu coud prove that the system is cut coherent.\n"
  else print_string "\nThe system is NOT cut coherent.\n"
;;

let check_initialcoherence system_name spec = 
  let coherent = Hashtbl.fold (fun conn specs res -> 
    let d = Coherence.checkInitCoher system_name conn specs spec
    in
    if d then print_string ("====> Connective "^conn^" is initial-coherent.\n")
    else print_string ("x ==> Connective "^conn^" is not initial-coherent.\n");
    d && res 
  ) (Specification.getLRHash spec) true
  in
  if coherent then print_string "\nTatu could prove that the system is initial coherent.\n"
  else print_string "\nThe system is NOT initial coherent.\n"
;;

let check_scopebang () =
  print_endline "Please type the subexponential:";
  let s = read_line() in
  let ers = Subexponentials.erased_bang s in
  let ept = Subexponentials.empty_bang s in
  print_endline ("!"^s^"  : ");
  print_endline "The following will have their formulas erased: ";
  List.iter (fun a -> print_string (a^", ")) ers; print_newline ();
  print_endline "The following should be empty: ";
  List.iter (fun a -> print_string (a^", ")) ept; print_newline ();
;;








(* Auxiliary functions *)

let remove_elt e l =
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x::xs when e = x -> go xs acc
    | x::xs -> go xs (x::acc)
  in go l []
;;

let remove_duplicates l =
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x :: xs -> go (remove_elt x xs) (x::acc)
  in go l []
;;








(* Check polarity-of-body count for each logic in the proofsystems *)
let print_pole_count () = 
  let dir = "../examples/proofsystems" in
  let children = Array.to_list(Sys.readdir dir) in
  let children = List.map(fun child -> Str.split (Str.regexp "\\.") child) children in
  let children = List.filter(fun child -> 
    List.length child = 2 && (List.nth child 1 = "pl" || List.nth child 1 = "sig")) children in
  let children = remove_duplicates (List.map(fun child -> List.nth child 0)children) in
  let specs = List.map (fun file -> 
    fn := dir^"/"^file;
    initAll ();
    let spec = FileParser.parse !fn in
    let rules = Specification.getLRHash spec in
    let rulesM1 = Hashtbl.copy(rules) in
    let rulesM2 = Hashtbl.copy(rules) in 

    let rulesB1 = Hashtbl.copy(rules) in
    let rulesB2 = Hashtbl.copy(rules) in
    Hashtbl.filter_map_inplace (fun name (bl, br) -> 
      if Term.isBipole bl && Term.isBipole br 
         then Some (bl, br) else None) rulesB1;
    Hashtbl.filter_map_inplace (fun name (bl, br) -> 
      if (Term.isBipole bl && not (Term.isBipole br)) || (not (Term.isBipole bl) && Term.isBipole br) 
         then Some (bl, br) else None) rulesB2;
    let bip1 = 2*Hashtbl.length rulesB1 in
    let bip2 = Hashtbl.length rulesB2 in
    let bipoleNum = string_of_int (bip1 + bip2) in

    let rulesM1 = Hashtbl.copy(rules) in
    let rulesM2 = Hashtbl.copy(rules) in 
    Hashtbl.filter_map_inplace (fun name (bl, br) -> 
      if Term.isMonopole bl && Term.isMonopole br then Some (bl, br) else None) rulesM1;
    Hashtbl.filter_map_inplace (fun name (bl, br) -> 
      if (Term.isMonopole bl && not (Term.isMonopole br)) || (not (Term.isMonopole bl) && Term.isMonopole br) then Some (bl, br) else None) rulesM2;
    let monop1 = 2*Hashtbl.length rulesM1 in
    let monop2 = Hashtbl.length rulesM2 in 
    let monopNum = string_of_int (monop1 + monop2) in

    let neitherNum = string_of_int (2*Hashtbl.length(rules) - int_of_string bipoleNum) in
    (Specification.getName spec, monopNum, bipoleNum, neitherNum)
  ) children in 
  List.iter (fun (a,b,c,d) -> print_endline (a^"   Monopoles: "^b^"   Bipoles: "^c^"   Neither: "^d)) specs
;;

let permutationToTex f1 f2 cl = 
  let permutationTex pairs cl =
    (match cl with
     | false -> Permutation.permutationsToTexString pairs
     | true -> Permutation.permutationsToTexStringCl pairs) in
  let nonPermutationTex pairs cl =
    (match cl with
     | false -> Permutation.nonPermutationsToTexString pairs
     | true -> Permutation.nonPermutationsToTexStringCl pairs) in
  match Permutation.permute f1 f2 with
  | (true, [], []) -> 
     "Could not build a derivation with the two chosen rules.\n\n";

  | (true, pairs, []) -> 
     "The rules permute. Here are the permutations:\n" ^ 
       (permutationTex pairs cl);
     
  | (false, ok, notok) -> 
     "The rules might not permute.\n" ^
       "These are the configurations for which a permutation was found:\n" ^ 
         (permutationTex ok cl) ^
           "These are the configurations for which a permutation was not found:\n" ^
             (nonPermutationTex notok cl);
     
  | _ -> failwith ("Invalid result for permutation checking.")
;;

(* Functions related to the standard output, they are mainly
   used to provide strings to Quati's website *)
let print_rules_names spec =
  let names = Specification.getIntroRulesNames spec in
  List.iter (fun s ->
      print_endline s
    ) names
;;

let print_bipoles_cl spec =
  let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
  let bipoles = Bipole.get_bipoles formulas in
  List.iter (fun (pt, model) ->
      print_endline "\\[";
      print_endline (ProofTreeSchema.toTexString (pt));
      print_endline "\\]";
      print_endline "\\[";
      print_endline "CONSTRAINTS = ";
      print_endline (Constraints.toJaxString (model));
      print_endline "\\]";
    ) bipoles
;;

let print_olrules_cl spec =
  let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
  let bipoles = Bipole.get_bipoles formulas in
  List.iter (fun bipole ->
      (* TODO: this is always a list with one element, one bipole (which is a pair
    <proof_tree, model>. All methods in olRule should be modified to work with
    only one derivation at a time *)
      let olpt = apply_derivation bipole in
      print_endline "\\[";
      print_endline (OlProofTree.toTexString olpt);
      print_endline "\\]";
    ) bipoles
;;

(* Needed for debugging, only prints yes/no without showing the derivations *)
let print_permute_bool spec name1 name2 = 
  let formula1 = Specification.getSpecificationOf spec name1 in
  let formula2 = Specification.getSpecificationOf spec name2 in
  match Permutation.permute formula1 formula2 with 
  (* If both lists are empty, no bipoles could be constructed. *)
  | (true, [], []) -> print_endline "N/A."
  (* Else if there are no failures the second list should be empty. *)
  | (true, pairs, []) -> print_endline "Yes.";
  (* Else, some permutation was not possible. *)
  | (false, _, bipoles) -> print_endline "No.";
  | _ -> failwith ("Invalid result for permutation checking.")
;;

let print_permutation_cl spec name1 name2 = 
  let formula1 = Specification.getSpecificationOf spec name1 in
  let formula2 = Specification.getSpecificationOf spec name2 in
  print_endline (permutationToTex formula1 formula2 true)
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

(* file output related *)
let fprint_olrules bipoles file_name =
  let file = open_out (file_name ^ ".tex") in
  Printf.fprintf file "%s" Prints.texFileHeader;
  List.iter (fun bipole ->
      (* TODO: this is always a list with one element, one bipole (which is a pair
      <proof_tree, model>. All methods in olRule should be modified to work with
      only one derivation at a time *)
      let olpt = apply_derivation bipole in
      Printf.fprintf file "%s" "{\\scriptsize";
      Printf.fprintf file "%s" "\\[";
      Printf.fprintf file "%s" (OlProofTree.toTexString olpt);
      Printf.fprintf file "%s" "\\]";
      Printf.fprintf file "%s" "}";
    (*Printf.fprintf file "Constraints: %s" (Constraints.toTexString model);*)
    ) bipoles;
  Printf.fprintf file "%s" Prints.texFileFooter;
  close_out file
;;

let fprint_bipoles bipoles file_name = 
  let file = open_out (file_name ^ ".tex") in
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

let fprint_permutation forms_lst file_name =
  let file = open_out (file_name ^ ".tex") in
  Printf.fprintf file "%s" Prints.texFileHeader;
  List.iter (fun (f1, f2) ->
      let name1 = Term.getRuleName f1 in
      let name2 = Term.getRuleName f2 in
      Printf.fprintf file "\\section{Permutation of $%s$ and $%s$}\n\n" name1 name2;
      Printf.fprintf file "%s" (permutationToTex f1 f2 false);
    ) forms_lst;
  Printf.fprintf file "%s" Prints.texFileFooter;
  close_out file
;;

(* Functions related to the download option of Quati's website *)
let permute_to_file spec name1 name2 =
  let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
  let index = ref (-1) in
  let counter () = index := !index + 1; !index in
  let i1 = ref 0 in
  let i2 = ref 0 in
  List.iter (fun f -> 
      if (Term.getRuleName f) = name1 then i1 := counter()
      else begin
          if (Term.getRuleName f) = name2 then i2 := counter()
          else index := !index + 1;
        end
    );
  fprint_permutation [((List.nth formulas !i1), (List.nth formulas !i2))] "permutation"
;;

let rules_to_file spec =
  let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
  let bipoles = Bipole.get_bipoles formulas in
  fprint_olrules bipoles "rules"
;;

let bipoles_to_file spec =
  let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
  let bipoles = Bipole.get_bipoles formulas in
  fprint_bipoles bipoles "bipoles"
;;

let print_help () = 
  print_endline "\n* The following commands are available during state ':>':\n";
  print_endline "#load location-of-file (without extensions .sig nor .pl): loads \
    the corresponding program;";
  print_endline "#verbose on or #verbose off: turns on or off the printing of \
    some steps of the computation. The default value is 'off';";
  (*print_endline "#time on or #time off: turns on or off the measuring of the
  execution time of a query. The default value is 'off'. (Note that the time
  measurement of the permutation checking is always on);";*)
  print_endline "#help displays this message.";
  print_endline "#monopoles provides a count on the number of monopoles for each logic.";
  print_endline "#exit terminates the program.";
  
  print_endline "\n* The following commands are available during state 'file_name >':";
  
  print_endline "\n** Helper commands **";
  print_endline "#check_rules: checks if all the rules of a file are bipoles.";
  print_endline "#check_polarity: checks all formulas of selected logic for monopole, bipole, or niether";
  print_endline "#scopebang: prints which subexponentials will have their \
    formulas erased and which should be empty when a !s formula is going to be \
    used.";
  print_endline "#done: you must type this to indicate that you are done working \
    with a file and before loading another one.\n";
  print_endline "#help displays this message.";
  print_endline "#exit terminates the program.";
  
  print_endline "\n** Quati commands **";
  print_endline "#rule: prints the selected object logic rule to a LaTeX file.";
  print_endline "#rules: prints all object logic rules to a LaTeX file.";
  print_endline "#bipole: prints the bipole of the selected rule to a LaTeX file";
  print_endline "#bipoles: prints the bipoles of all rules to a LaTeX file.";
  print_endline "#permute: checks if two rules of your choice permute.";
  print_endline "#permute_all: checks the permutation of all rules of the system.";
  print_endline "#permutation_cliques: computes the permutation cliques (sets of rules such that \
    every rules permutes over each other) and prints one per line.";
  print_endline "#permutation_dot_graph: generates a permutation graph in dot format of all rules of the system.";
  print_endline "#permutation_table: generates a latex file with a table containing the permutation between all \
    the rules in the system.";

  print_endline "\n** Tatu commands **";
  print_endline "#principalcut: checks if the rules can permute until the cut becomes principal.";
  print_endline "#cutcoherence: checks whether the system specified on the file loaded is cut-coherent.";
  print_endline "#initialcoherence: checks whether the system specified on the file loaded is initial-coherent.";
  print_endline "#atomicelim: checks whether the system specified on the file loaded is weak coherent.";
  print_endline ""
;;


let rec start () =
  initAll ();
  print_string ":> ";
  let command = read_line () in
    try 
      let lexbuf_top = Lexing.from_string command in 
      let action = Parser.top Lexer.token lexbuf_top in 
      match action with
      | "verbose-on" -> print_endline "Verbose is set to on."; Term.verbose := true; start ()
      | "verbose-off" -> print_endline "Verbose is set to off."; Term.verbose := false; start ()
      | "time-on" -> Term.time := true; print_endline "Time is set to on."; start ()
      | "time-off" -> Term.time := false; print_endline "Time is set to off."; start ()
      | "help" -> print_help ();
      | "monopoles" -> print_pole_count(); start ()
      | "exit" -> print_endline "Thank you for using SELLF."; exit 1
      | file_name -> 
        print_endline ("Loading file "^file_name);
        let spec = FileParser.parse file_name in
          samefile := true;
          while !samefile do 
            solve_query spec; 
          done
    with
    |  Parsing.Parse_error ->  print_endline "Invalid command. For more information type #help."; start  ()
    |  Sys_error str -> print_string ("Error"^str); print_endline ". Please double check the name of the file."; start ()
and
solve_query spec = 
  let sysName = Specification.getName spec in
  print_string (sysName ^ " > ");
  let query_string = read_line () in
  if query_string = "#done" then samefile := false
  else begin
  match query_string with

    | "#help" -> print_help ();
    | "#exit" -> print_endline "Thank you for using SELLF."; exit 1

    | "#coqspec" ->
      let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
      let coqspec = Sellf2coq.sellf2coq (Specification.getUserTypes spec) formulas in
      print_newline ();
      print_endline "Warning! This is work in progress. Only a partial \
      specification will be generated.";
      print_newline ();
      print_endline "The specification of this system in Coq will be printed \
      in a file. What shall it be called?";
      let filename = read_line () in
      let file = open_out (filename ^ ".v") in
      Printf.fprintf file "%s" (coqspec);
      close_out file

    (* Generates the bipole of a rule of the object logic and prints a latex file with it *)
    | "#bipole" -> 
      let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
      print_formulas formulas;
      print_endline "The bipoles for the chosen formula will be generated and \
      printed to a LaTeX file.\nPlease choose a formula by its number:";
      let i1 = int_of_string (read_line ()) in
      print_endline "Please choose a name for the file:";
      let f = read_line () in
      let bp = Bipole.bipole (List.nth formulas i1) in
      fprint_bipoles bp f

    (* Generates all bipoles of all rules of the object logic and prints a latex file with them *)
    | "#bipoles" ->
      print_newline ();
      print_endline "All the bipoles of the specification will be generated \
      and printed in a latex file.\nPlease choose a name for the file:";
      let f = read_line () in
      let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
      let bipoles = Bipole.get_bipoles formulas in
      fprint_bipoles bipoles f

    (* Check if all rules are bipoles *)
    | "#check_rules" -> 
      let formulas = Specification.getRules spec in
      let not_bipoles = List.filter (fun f -> not (Term.isBipole f)) formulas in
      begin match not_bipoles with
        | [] -> print_endline ("All formulas are bipoles.")
        | _ -> List.iter (fun f -> 
          print_endline ("The following formula is NOT a bipole: " ^ (Prints.termToString f)) 
        ) not_bipoles 
      end

    (* Check the polarity of rules in the given logic *)
    | "#check_polarity" -> 
      let hash_formulas = Specification.getLRHash spec in
      print_endline ("Number of rules: "^string_of_int (2*Hashtbl.length hash_formulas));
      Hashtbl.iter (fun name value -> 
          let (left_body, right_body) = value in  
          if Term.isMonopole left_body then
          print_endline (name^"_left: monopole")
          else if Term.isBipole left_body then 
          print_endline (name^"_left: bipole")
          else 
          print_endline (name^"_left: neither");
          if Term.isMonopole right_body then
          print_endline (name^"_right: monopole")
          else if Term.isBipole right_body then 
          print_endline (name^"_right: bipole")
          else 
          print_endline (name^"_right: neither")
        ) hash_formulas

    (* Generates a rule of the object logic and prints a latex file with it *)
    | "#rule" -> 
      let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
      print_formulas formulas;
      print_endline "The object logic rule of the chosen formula will be generated and \
      printed to a LaTeX file.\nPlease choose a formula by its number:";
      let i1 = int_of_string (read_line ()) in
      print_endline "Please choose a name for the file:";
      let f = read_line () in
      let bp = Bipole.bipole (List.nth formulas i1) in
      fprint_olrules bp f

    (* Generates all rules of the object logic and prints a latex file with them *)
    | "#rules" ->
      print_newline ();
      print_endline "The object logic rules of all the formulas of the specification \
      will be generated and printed in a latex file.\nPlease choose a name for the file:";
      let f = read_line () in
      let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
      let bipoles = Bipole.get_bipoles formulas in
      fprint_olrules bipoles f

    (* Check if two rules permute *)
    | "#permute" -> 
      let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
      print_formulas formulas;
      print_endline "Checking whether a rule R1 permutes up a rule R2.\n";
      print_endline "Please type the number of R1: ";
      let i1 = int_of_string (read_line ()) in
      print_endline "Please type the number of R2: ";
      let i2 = int_of_string (read_line ()) in
      print_endline "Please type a file name for the results:";
      let f = read_line () in
      fprint_permutation [((List.nth formulas i1), (List.nth formulas i2))] f

    (* Check if all rules permute *)
    | "#permute_all" ->
      let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
      print_endline "Checking the permutation of all formulas over all \
      formulas.\nPlease type a file name for the results:";
      let f = read_line () in
      let pairs = List.fold_right (fun f1 acc -> 
        List.fold_right (fun f2 acc2 ->
          (f1, f2) :: acc2 
        ) formulas acc
      ) formulas [] in
      fprint_permutation pairs f

    (* Prints all sets of rules (one per line) such that all rules within one
     * set permute over each other.
     *)
    | "#permutation_cliques" ->
      print_newline ();
      print_endline "Rules belonging to the same group permute over each other.";
      print_endline "Ci < Cj iff every rule rj in Cj permutes up every rule ri in Ci, i.e., rj -> ri in G.";
      print_endline "This may take a while, please be patient...\n";
      let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
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
      let file = open_out (filename ^ ".dot") in
      let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
      Printf.fprintf file "%s" (Permutation.getPermutationDotGraph formulas);
      close_out file

    | "#permutation_table" ->
      print_newline ();
      print_endline "The permutation table of all rules of the specification \
      will be generated in the tex format and printed to a file.\nPlease choose \
      a name for the file:";
      let filename = read_line () in
      let file = open_out (filename ^ ".tex") in
      let formulas = (Specification.getIntroRules spec) @ (Specification.getStructRules spec) in
      Printf.fprintf file "%s" (Permutation.getPermutationTable formulas);

    | "#cutcoherence" -> check_cutcoherence sysName spec
    
    | "#initialcoherence" -> check_initialcoherence sysName spec

    | "#scopebang" -> check_scopebang ()

    | "#atomicelim" -> check_atomicelim spec 

    | "#principalcut" -> check_principalcut spec

    (* Query *)
    | _ ->
      let query = Lexing.from_string query_string in
      try
        let g = Parser.goal Lexer.token query in
        let _ = typeCheck g (Specification.getTypes spec) in
        let goal = deBruijn g in
          Context.createProofSearchContext spec;
          if Boundedproofsearch.prove goal !Term.psBound (fun () -> true) (fun () -> false) then
            print_string "\nYes.\n"
          else print_string "\nNo.\n"
      with
      | Parsing.Parse_error -> Format.printf "Syntax error%s.\n%!" (FileParser.position query); solve_query spec
      | Failure str -> Format.printf "ERROR:%s\n%!" (FileParser.position query); print_endline str; start()

    (*| _ -> print_endline "Function not implemented. Try again or type #done
     * and #help."*)

  end

(*********** FOR BATCH MORE PROCESSING ************)

let fileName = ref "" ;;
let check = ref "" ;;
let rule1 = ref "" ;;
let rule2 = ref "" ;;

let usage = "Usage: " ^ Sys.argv.(0) ^ " [-v] [-i string] [-c string]"

let argslst = [
  ("-v", Arg.Unit (fun () -> Term.verbose := true), ": set verbose on.");
  ("-i", Arg.String (fun s -> fileName := s), ": prefix of .pl and .sig file (with path)");
  ("-c", Arg.String (fun s -> check := s), ": 'principalcut', 'cutcoherence', 'initialcoherence', 'atomicelim', 'scopebang', 'rulenames', 'permute', 'bipoles' or 'rules' (depending on what you want to check)");
  ("-r1", Arg.String (fun r -> rule1 := r), ": set the name of the first rule to check the permutation above the second rule.");
  ("-r2", Arg.String (fun r -> rule2 := r), ": set the name of the second rule.");
  ("-bipole", Arg.Unit (fun () -> Permutation.setShowBipole true), ": show bipole.");
]

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
    let spec = FileParser.parse file in
    begin
      print_endline "SELLF -- A linear logic framework for systems with locations.";
      print_endline "Version 0.5.\n";
      print_endline "Type #help for a list of available commands.\n";
      print_endline ("The file: " ^ file ^ " was loaded.\n");
      samefile := true;
      while !samefile do 
        solve_query spec
      done;
      while true do
        start ()
      done
    end
  (* Running in batch mode *)
  | ("principalcut", file, _, _) -> 
    initAll ();
    check_principalcut (FileParser.parse file)
  | ("cutcoherence", file, _, _) -> 
    let idx = String.rindex file '/' in
    let specName = Str.string_after file (idx+1) in
    initAll ();
    check_cutcoherence specName (FileParser.parse file)
  | ("initialcoherence", file, _, _) -> 
    let idx = String.rindex file '/' in
    let specName = Str.string_after file (idx+1) in
    initAll ();
    check_initialcoherence specName (FileParser.parse file)
  | ("atomicelim", file, _, _) -> 
    initAll ();
    check_atomicelim (FileParser.parse file)
  | ("scopebang", file, _, _) ->
    initAll ();
    let _ = FileParser.parse file in
    check_scopebang ()
  | ("bipoles", file, _, _) ->
    initAll ();
    print_bipoles_cl (FileParser.parse file)
  | ("rules", file, _, _) ->
    initAll ();
    print_olrules_cl (FileParser.parse file)
  | ("permute", file, r1, r2) ->
    initAll ();
    print_permutation_cl (FileParser.parse file) r1 r2
  | ("rulenames", file, _, _) ->
    initAll ();
    print_rules_names (FileParser.parse file)
  | ("permutebin", file, r1, r2) ->
    initAll ();
    print_permute_bool (FileParser.parse file) r1 r2
  | ("bipoles_to_file", file, _, _) ->
    initAll ();
    bipoles_to_file (FileParser.parse file)
  | ("rules_to_file", file, _, _) ->
    initAll ();
    rules_to_file (FileParser.parse file)
  | ("permute_to_file", file, r1, r2) ->
    initAll ();
    permute_to_file (FileParser.parse file) r1 r2
  | ("parse", file, _, _) ->
    initAll ();
    (try let _ = FileParser.parse file in
      print_endline "Yes."
    with
    | _ -> print_endline "No." )
  | (x, y, _, _) -> failwith ("Invalid arguments.")
;;

