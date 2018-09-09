(* File lexer.mll *)
{
open Parser
exception Eof
open Lexing 

exception ReservedKeyword of string

let incrline lexbuf =
    lexbuf.lex_curr_p <- {
    lexbuf.lex_curr_p with
    pos_bol = lexbuf.lex_curr_p.pos_cnum;
    pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }
}

(* comments start with % *)
let comment = ['%'] [^'\n']* '\n'

(* valid names start with lower case letters and can contain numbers *)
let valid_name = ['a' - 'z'] ['a' - 'z' 'A' - 'Z' '0' - '9']* 

(* variables start with upper case letters and can contain numbers or _ *)
let var_name = ['A' - 'Z'] ['a' - 'z' 'A' - 'Z' '0' - '9' '_']*

(* LaTeX code corresponding to a connective *)
let connectiveTex = ['\\']+ ['a' - 'z' 'A' - 'Z' '0' - '9' '*']*

(* File path can be anything (TODO: find the correct regex to use here) *)
let filepath =  [^' ']+

let subtype =  "lin"  |  "aff" | "rel" | "unb"
let ctxtype = "many"  |  "single"
let ctxside = "ant" | "suc" | "antsuc"

rule token = parse 

[' ' '\t' '\r']         { token lexbuf }
| comment               { incrline lexbuf; token lexbuf }
| connectiveTex as ct   { CONNTEX(ct) }
| '\n'                  { incrline lexbuf; token lexbuf }

(* Reserved keywords for files *)
| "kind"                { KIND }
| "type"                { TYPE }
| "tsub"                { TSUBEX }
| "subexp"              { SUBEX }
| "subexpctx"           { SUBEXCTX }
| ctxtype as t          { CTXTYPE(t) }
| ctxside as s          { CTXSIDE(s) }
| "context"             { CONTEXT }      
| "subexprel"           { SUBEXPREL }
| "pos"                 { POS }
| "neg"                 { NEG }
| "rules"               { RULES }
| "axiom"               { AXIOM }
| "cut"                 { CUTRULE }
| "structural"          { STRUCTURAL }
| "introduction"        { INTRODUCTION }
| "gamma"               { GAMMA }
| "infty"               { INFTY }
| subtype as s          { TSUB(s) }

(* Reserved keywords for the top-level *)
| "#load " (filepath as s) { LOAD(s) }
| "#help"               { HELP }
| "#verbose"            { VERBOSE }
| "#time"               { TIME }
| "on"                  { ON }
| "off"                 { OFF }
| "#exit"               { EXIT }
| "#monopoles"         { POLES }

(* Built-in types *)
| "int"                 { TINT }
| "list"                { TLIST }
| "string"              { TSTRING }

(* Symbols *)
| "->"                  { TARR }
| '.'                   { DOT }
| '('                   { LPAREN }
| ')'                   { RPAREN }
| '['                   { LBRACKET }
| ']'                   { RBRACKET }
| '{'                   { LCURLY }
| '}'                   { RCURLY }
| "<"                   { LESS }
| ">="                  { GEQ }
| ';'                   { SEMICOLON }
| "_"                   { UNDERSCORE }
| '"'                   { QUOTE }
| ','                   { COMMA }

(* LL connectives *)
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

(* Constraints predicates *)
| "in"                  { IN } 
| "in_unique"           { INUNQ }
| "in_final"            { INFINAL }
| "emp"                 { EMP }
| "union"               { UNION }
| "minus"               { SETMINUS }
| "contained"           { CONTAINED }
| "max_index"           { MAXIDX }
| "not_max_index"       { NOTMAXIDX }

(* Others *)
| valid_name as s       { NAME(s) }
| var_name as s         { VAR(s) }
| ['0'-'9']+ as s       { INT(int_of_string s) }
| eof                   { EOF }


