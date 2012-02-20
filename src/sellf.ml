open ProofTree
open Context
open Subexponentials

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

let rec start () =
    Term.initialize ();
    Context.initialize ();
    (*Structs.initialize ();
    Coherence.initialize ();
    Structs.rules := [];*)
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
        begin
          fileName := file_name;
          print_endline ("Loading file "^file_name);
          let file_sig = open_in (file_name^".sig") in
          let lexbuf = Lexing.from_channel file_sig in
          begin
            try 
              while true do
                let _ = Parser.types Lexer.token lexbuf in ();
              done
            with 
              |  Lexer.Eof -> 
                  let file_prog = open_in (file_name^".pl") in 
                  let lexbuf = Lexing.from_channel file_prog in
                    begin
                    try
                      while true do
                        let _ = Parser.clause Lexer.token lexbuf in ();
                      done  
                    with 
                      | Lexer.Eof -> samefile := true; (*Structs.saveInitState ();*)
                        while !samefile do 
                          solve_query (); 
                          (*Structs.recoverInitState () *)
                        done
                      | Parsing.Parse_error ->  Format.printf "Syntax error while parsing .pl file%s.\n%!" (position lexbuf); start ()
                      | Failure str -> Format.printf ("ERROR:%s\n%!") (position lexbuf); print_endline str; start ()
                    end
              |  Parsing.Parse_error ->  Format.printf "Syntax error while parsing .sig file%s.\n%!" (position lexbuf); start ()
              |  Failure _ -> Format.printf "Syntax error%s.\n%!" (position lexbuf); start ()
            end
        end
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
    (*
    | "#macro" -> 
      print_endline "Generating macro rules...";
      let n = ref 1 in
      let rec gen_macros rls = match rls with
        | [] -> print_endline "\nDone."
        | hd :: tl ->
          Macro.initMacro hd;
          print_string "\nMacro rule(s) for term: "; 
          Prints.print_term hd; print_newline (); 
          Macro.rmacro (fun () ->
            ProofTree.printLeaves !Macro.macrorule;
            flush stdout;
            Constraints.printConstraints !Macro.constrs;
            flush stdout;
            Constraints.genSolverInput !Macro.constrs !n;
            n := !n + 1;
            print_string "End of Macro.\n";
            Macro.save_macro ()
            );
          gen_macros tl
          in gen_macros !Structs.rules;
		      (* Printing the results... *)
          (*let macro_file = open_out ("viewer/macro.xml") in*)
          print_endline ("Number of macro rules: "^(string_of_int (List.length !Macro.macrolst)));
		      let tex_file = open_out ("viewer/macro.tex") in
		      (*let jit_file = open_out ("viewer/macro.jit") in*)
          (*ProofTree.printTreesMacros !Structs_macro.macrolst macro_file; *)
          ProofTree.printTexMacros !Macro.macrolst tex_file;
          close_out tex_file;
          (*ProofTree.printJitMacros !Structs_macro.macrolst jit_file;*)

    | "#perm" ->
      let tryPermute a b = 
        print_endline "\nLet ";
        print_string "r1 = "; Prints.print_term a; print_string " and \n";
        print_string "r2 = "; Prints.print_term b; print_string "\n";
        flush stdout;
	      let start_time = Sys.time () in
        try match Permutation.permute a b with
          | true -> 
	          let end_time = Sys.time () in
	          let total = end_time -. start_time in
            print_endline "Then r1 permutes over r2.";
	          Printf.printf "Execution time: %f seconds.\n" total
          | false -> 
	          let end_time = Sys.time () in
	          let total = end_time -. start_time in
            print_endline "Then, r1 does NOT permute over r2.";
	          Printf.printf "Execution time: %f seconds.\n" total
          with s -> 
	          let end_time = Sys.time () in
	          let total = end_time -. start_time in
            (* TODO: give more information on this error. *)
            print_endline ("Error: "^(Printexc.to_string s));
	          Printf.printf "Execution time: %f seconds.\n" total
      in

      (* Checking permutation of every pair of rules in the file *)
      let rec every_pair forms = match forms with
        | [] -> print_endline "Done."
        | hd :: tl ->
          (* Checking the formula with itself *)
          (* This makes no sense yet because both formulas use the same
          constants *)
          (* TODO: allow the specification to be done with variables and
          instantiate fresh constants for each variable. *)
          (*tryPermute hd hd;*)
          
          let rec check_perm f lst = match lst with
            | [] -> ()
            | h :: t -> 
              tryPermute f h;
              tryPermute h f;
              check_perm f t    

          in check_perm hd tl; every_pair tl
      in every_pair !Structs.rules;
    *)
    | "#coherence" ->
      if !Coherence.seqcalc then
        Coherence.check !fileName
      else
        print_string "\nCannot prove coherence (please check the correct use of the predicates).\n";

    | "#scopebang" -> begin
      print_endline "Please type the subexponential:";
      let s = read_line() in
      let ers = Subexponentials.erased_bang s in
      let ept = Subexponentials.empty_bang s in
      print_endline ("!"^s^"  : ");
      print_endline "The following will have their formulas erased: ";
      List.iter (fun a -> print_string (a^", ")) ers; print_newline ();
      print_endline "The following should be empty: ";
      List.iter (fun a -> print_string (a^", ")) ept; print_newline ();
      end

    | _ -> failwith "Function not implemented."

    (*
    | _ -> begin
      let query = Lexing.from_string query_string in
      begin
      try 
        let _ = Parser.goal Lexer.token query in ();
	      (*if !Structs.time then begin
	        let start_time = Sys.time () in
                Interpreter.solve (fun () -> 
                  if (Interpreter.empty_nw ()) then 
                    print_string "\nYes.\n"
                  else (Structs.last_fail ()))  
                  (fun () -> print_string "\nNo.\n");
	        let end_time = Sys.time () in
	        let total = end_time -. start_time in
	        Printf.printf "Execution time: %f seconds.\n" total
        end
	      else*) 
          begin
          (*let term = List.hd (!Structs.goals) in*)
          Interpreter.initProof !Structs.goals;
          let proof_file = open_out "viewer/proof.xml" in
          let tex_file = open_out "viewer/proof.tex" in
          (*let jit_file = open_out "viewer/proof.jit" in*)
          let loop = ref true in
          let fail = ref (
            Interpreter.solve (fun () ->
              (* TODO: this emtiness is checked on the condition_init function,
              we should not deal with it here. Check interpreter functionality *)
              (*if (Structs.empty_nw ()) then begin*) 
                loop := false; 
                print_string "\nYes.\n";
                ProofTree.printTree Interpreter.proof proof_file; 
                ProofTree.printTexProof Interpreter.proof tex_file;
                (*ProofTree.printJitTree Interpreter.proof jit_file*)
              (*end
              else (Structs.last_fail ())*) )  
              (fun () -> loop := false; print_string "\nNo.\n") )
          in
          while !loop do 
            let res = !fail () in
            fail := fun () -> res
          done;
          (*
          Interpreter.solve (fun () -> 
            if (Interpreter.empty_nw ()) then 
              print_string "\nYes.\n"
            else (Structs.last_fail ()))  
            (fun () -> print_string "\nNo.\n");
          *)
        end
      with
        | Parsing.Parse_error -> Format.printf "Syntax error%s.\n%!" (position query); solve_query ()
        | Failure str -> Format.printf "ERROR:%s\n%!" (position query); print_endline str; start()
      end
      *)
    end
    (*end*)

let _ = 
print_endline "SELLF -- A linear logic framework for systems with locations.";
print_endline "Version 0.5.\n";
while true do
start ()
done

