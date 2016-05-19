(* 
 * Definition of tokes for the parsing of DLV models
 *
 * Giselle Reis
 * 2013
 * 
 * *)

{
  open Parser_models
}

let cstName = ['a' - 'z']+ ['a' - 'z' 'A' - 'Z' '0' - '9']*
let varName = ['A' - 'Z']+ ['a' - 'z' 'A' - 'Z' '0' - '9' '_']*
let index = ['0' - '9']+

rule token = parse
  | [' ' '\t' '\r']  { token lexbuf }
  (* Constraints predicates *)
  | "in"                { IN } 
  | "in_unique"         { INUNQ }
  | "in_final"          { INFINAL }
  | "emp"               { EMP }
  | "union"             { UNION }
  | "minus"             { SETMINUS }
  | "contained"         { CONTAINED }
  | "max_index"         { MAXIDX }
  | "not_max_index"     { NOTMAXIDX }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | '{'                 { LCURLY }
  | '}'                 { RCURLY }
  (* Names of contexts *)
  | "_"            { UNDERSCORE }
  | index as idx   { INDEX(int_of_string idx) }
  (* Formulas *)
  | "top"                 { TOP }
  | "bot"                 { BOT }
  | "one"                 { ONE }
  | "zero"                { ZERO }
  | "!"                   { BANG }
  | "?"                   { QST }
  | "all"                 { FORALL }     
  | "exs"                 { EXISTS }     
  | '*'                   { TIMES }
  | '+'                   { PLUS }
  | "|"                   { PIPE }
  | '&'                   { WITH }
  | "-o"                  { LOLLI }
  | "not"                 { NOT }
  | ":-"                  { INVLOLLI } 

  | '"'                   { QUOTE }
  | ','                   { COMMA }
  | varName as vn         { VAR(vn) }
  | '['                   { LBRACKET }
  | ']'                   { RBRACKET }
  | '\n'                  { NEWLINE }
  | cstName as cn  { NAME(cn) }
  | eof          { raise End_of_file }

