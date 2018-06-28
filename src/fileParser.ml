open Specification

let position lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let file = curr.Lexing.pos_fname in
  let line = curr.Lexing.pos_lnum in
  let char = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  if file = "" then
    () (* lexbuf information is rarely accurate at the toplevel *)
  else
    print_string ""; Format.sprintf "line %d, character %d" line char

let parse file_name =
  let file_sig = open_in (file_name^".sig") in
  let lexbuf = Lexing.from_channel file_sig in
  try
    let (kt, tt) = Parser.signature Lexer.token lexbuf in
      let file_prog = open_in (file_name^".pl") in 
      let lexbuf = Lexing.from_channel file_prog in
      try
        let (s, c, i, a) = Parser.specification Lexer.token lexbuf in
          Specification.create (file_name, kt, tt, s, c, i, a)
      with
      | Parsing.Parse_error -> failwith ("Syntax error while parsing .pl file: " ^ (position lexbuf))
      | Failure str -> failwith ("[ERROR] " ^ (position lexbuf))
  with
  | Parsing.Parse_error -> failwith ("Syntax error while parsing .sig file: " ^ (position lexbuf))
  | Failure _ -> failwith ("[ERROR] " ^ (position lexbuf))
;;
