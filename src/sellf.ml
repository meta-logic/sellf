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
      "" (* lexbuf information is rarely accurate at the toplevel *)
    else
      Format.sprintf ": file %s, line %d, character %d" file line char

(* TODO: fix the flow so that the user can ask several queries for the same file *)
let rec start () = 
    print_string ":> ";
    let command = read_line() in
    try 
      let lexbuf_top = Lexing.from_string command in 
      let action = Parser.top Lexer_top.token lexbuf_top in 
      match action with
      | "help" -> start ()
      | "verbose-on" -> Structs.verbose := true; print_endline "Verbose is set to on."; start ()
      | "verbose-off" -> Structs.verbose := false; print_endline "Verbose is set to off."; start ()
      | file_name -> 
        begin
          print_endline ("Loading file"^file_name);
          let file_sig = open_in (file_name^".sig") in
          let lexbuf = Lexing.from_channel file_sig in
          begin
            try 
              while true do
                Parser.types Lexer.token lexbuf
              done
            with 
              |  Lexer.Eof -> 
                  let file_prog = open_in (file_name^".pl") in 
                  let lexbuf = Lexing.from_channel file_prog in
                    begin
                    try
                      while true do
                        Parser.clause Lexer.token lexbuf
                      done  
                    with 
                      | Lexer.Eof -> solve_query ()
                      | Parsing.Parse_error ->  Format.printf "Syntax error while parsing .pl file.%s.\n%!" (position lexbuf); start ()
                      | Failure str -> Format.printf ("ERROR:%s\n%!") (position lexbuf); print_endline str; start ()
                    end
              |  Parsing.Parse_error ->  Format.printf "Syntax error while parsing .sig file. %s.\n%!" (position lexbuf); start ()
              |  Failure _ -> Format.printf "Syntax error%s.\n%!" (position lexbuf); start ()
              |  Sys_error str -> print_string ("Error"^str); print_endline ". Please double check the name of the file."; start ()
            end
        end
    with
    |  Parsing.Parse_error ->  print_endline "Invalid command. For more information type #help."; start  ()
and
solve_query () = 
    print_string "?> ";
    let query_string = read_line() in
    let query = Lexing.from_string query_string in
      begin
      try 
        Parser.goal Lexer.token query;
        Interpreter.solve (fun () -> 
          if (Interpreter.empty_nw ()) then 
            print_string "\nYes.\n"
          else (Structs.last_fail ())) 
          
          (fun () -> print_string "\nNo.\n")
      with
        | Parsing.Parse_error -> Format.printf "Syntax error%s.\n%!" (position query); solve_query ()
        | Failure str -> Format.printf "ERROR:%s\n%!" (position query); print_endline str; start()
      end

let _ = 
print_endline "SELLF -- A linear logic framework for systems with locations.";
print_endline "Version 0.5.\n";
while true do
start ()
done

