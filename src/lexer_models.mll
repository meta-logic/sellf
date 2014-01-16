(* 
 * Definition of tokes for the parsing of DLV models
 *
 * Giselle Machado Reis
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
  | "in"         { IN } 
  | "elin"       { ELIN }
  | "emp"        { EMP }
  | "union"      { UNION }
  | '('          { LPAREN }
  | ')'          { RPAREN }
  | '{'          { LCURLY }
  | '}'          { RCURLY }
  (* Names of contexts *)
  | "_"            { UNDERSCORE }
  | index as idx   { INDEX(int_of_string idx) }
  (* Formulas *)
  | '"'                   { QUOTE }
  | "-o"                  { LOLLI }
  | ','                   { COMMA }
  | '*'                   { TIMES }
  | '+'                   { PLUS }
  | "|"                   { PIPE }
  | '&'                   { WITH }
  | "top"                 { TOP }
  | "bot"                 { BOT }
  | "one"                 { ONE }
  | "zero"                { ZERO }
  | "pi \\" (varName as vn)        { FORALL(vn) }     
  | "sigma \\" (varName as vn)     { EXISTS(vn) }
  | "hbang"               { HBANG }
  | "bang"                { BANG }
  | "?"                   { QST }
  | "not"                 { NOT }
  | "nsub \\" (varName as vn) { NEW(vn) } 
  | '\\' (varName as lxm) { ABS(lxm) }
  | varName as vn         { VAR(vn) }
  | '['                   { LBRACKET }
  | ']'                   { RBRACKET }
  | '\n'                  { NEWLINE }
  | cstName as cn  { NAME(cn) }
  | eof          { raise End_of_file }

