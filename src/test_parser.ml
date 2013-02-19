(* File for testing the parser for constraints *)
(* Assumes the parser file is "parser_models.mly" and the lexer file is "lexer_models.mll". *)
let main () =
try
let lexbuf = Lexing.from_channel stdin in
while true do
  Parser_models.model Lexer_models.token lexbuf
  (*let m = Parser_models.model Lexer_models.token lexbuf in
  let c = Constraints.create m in
  print_endline "Parsed:";
  print_endline (Constraints.toString c)*)
  done
  with End_of_file -> exit 0
  let _ = Printexc.print main ()

