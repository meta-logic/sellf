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

(*let _ = 
  let t1 = Term.APP(Term.CONS("c"), [Term.INT(2)]) in
  let varX = Term.V {Term.str = "X"; Term.id = 0; Term.ts = 0; Term.tag = Term.LOG; Term.lts = 0} in
  let t2 = Term.APP(Term.CONS("c"), [Term.PTR {contents = varX}]) in 
  Term.print_term t1; Term.print_term t2; 
  TestUnify.unify t1 t2; Term.print_term t2*)


(*let _ = 
  let t1 = Term.ABS("X", 1,Term.DB(1)) in
  let t2 = Term.ABS("Y", 1, Term.ABS("Z",1, Term.DB(1))) in
  let t3 = Term.ABS("W", 1, Term.TENSOR(Term.FORALL("T",1,Term.DB(1)), Term.DB(1))) in
  let t4 = Term.ABS("X", 1, Term.APP(Norm.hnorm t3, [Term.DB(1)])) in
  let pred = Term.ABS("X", 1, Term.PRED("name", Term.APP(Term.CONS "name", [Term.DB(1)]))) in
  let t2 = Term.ABS("X", 1,Term.APP(Term.ABS("f", 1, Term.DB(1)), [t1])) in 
  let t5 = Term.CONS("c") in 
  let tn1 = Norm.hnorm t3 in
  let t6 = Term.APP(Norm.hnorm t4,[t5]) in
  let tn = Norm.hnorm t6 in
  let prednorm = Norm.hnorm (Term.APP(Norm.hnorm pred, [t5])) in
  print_string "\nTesting PRED: \n";
  Term.print_term pred; print_string " applied to "; Term.print_term t5; print_newline ();
  print_string "Result in: "; Term.print_term prednorm; print_newline (); print_newline ();
  Term.print_term t6; print_endline " ";
  Term.print_term tn; print_newline ();
  Term.print_term (Norm.hnorm t4)*)

let _ = 
  try 
    print_endline "Enter the name of program file (without extensions .sig nor ,pl):";
    let file_name = read_line() in 
    let file_sig = open_in (file_name^".sig") in
    let lexbuf = Lexing.from_channel file_sig in
    begin
    try 
      while true do
        Parser.types Lexer.token lexbuf
      done;
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
              |  Lexer.Eof -> ()
              |  Sys_error str -> print_string ("Error"^str); print_endline ". Please double check the name of the file."; exit 0
              |  Parsing.Parse_error ->  Format.printf "Syntax error%s.\n%!" (position lexbuf); exit 1
              |  Failure str -> Format.printf ("ERROR:%s\n%!") (position lexbuf); print_endline str; exit 1 
            end
      |  Parsing.Parse_error ->  Format.printf "Syntax error%s.\n%!" (position lexbuf); exit 1
      |  Failure _ -> Format.printf "Syntax error%s.\n%!" (position lexbuf); exit 1
    end
  with 
  |  Sys_error str -> print_string ("ERROR:"^str); print_endline ". Please double check the name of the file."; exit 0

(*let _ =  
  try 
    print_endline "Enter the name of program file (without extension .pl):";
    let file_prog = open_in (read_line()^".pl") in 
    let lexbuf = Lexing.from_channel file_prog in
    begin
    try
      while true do
        Parser.clause Lexer.token lexbuf
      done  
    with 
      |  Lexer.Eof -> ()
      |  Sys_error str -> print_string ("Error"^str); print_endline ". Please double check the name of the file."; exit 0
      |  Parsing.Parse_error ->  Format.printf "Syntax error%s.\n%!" (position lexbuf); exit 1
      |  Failure str -> Format.printf ("ERROR:%s\n%!") (position lexbuf); print_endline str; exit 1 
    end
  with
  |  Sys_error str -> print_string ("Error"^str); print_endline ". Please double check the name of the file."; exit 0*)
    
let _ = 
  print_endline "Enter the query:";
  let query = Lexing.from_channel stdin in
  begin
  try 
    Parser.goal Lexer.token query;
    Interpreter.solve (fun () -> 
      if (Interpreter.empty_nw ()) then 
        print_string "\nYes.\n"
      else (Structs.last_fail ())) 
      
      (fun () -> print_string "\nNo.\n")

      (*| true -> print_string "\nYes.\n"; ()
      | false -> print_string "\nNo.\n"; ()
      | _ -> print_string "Ooops.\n"; ()
    )*)
  with
    | Parsing.Parse_error -> Format.printf "Syntax error%s.\n%!" (position query); exit 1
    | Failure str -> Format.printf "ERROR:%s\n%!" (position query); print_endline str; exit 1
  end

    (*let lexbuf = Lexing.from_channel stdin in
      while true do
            let _ = Parser.types Lexer.token lexbuf in
            print_string "Types parsed.\n"; flush stdout;
          let _ = Parser.clause Lexer.token lexbuf in
          print_string "Clauses parsed.\n"; flush stdout;
            let _ = Parser.goal Lexer.token lexbuf in
            print_string "Goal parsed.\n";
                let result = Hashtbl.length Term.tTbl in
              let result2 = Hashtbl.length Term.kTbl in
              let result3 = Hashtbl.length Term.rTbl in
                let result4 = Stack.length Structs.goals in
                  print_string "Size of types table: "; print_int result; print_newline(); flush stdout;
                  print_string "Size of kinds table: "; print_int result2; print_newline(); flush stdout;
                  print_string "Size of rules table: "; print_int result3; print_newline(); flush stdout;
                    print_string "Size of goals stack: "; print_int result4; print_newline(); flush stdout;
            let g = Stack.pop Structs.goals in
                let res = Interpreter.solve_a (g::[]) in
                print_string " Solved? ";
                if res then print_string "Proved true." else print_string "Proved false."; 
                print_newline(); 
                flush stdout;
        done
    *)
