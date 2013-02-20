/* 
 * Parser for models generated by DLV
 *
 * Giselle Machado Reis 
 * 2013
 *
 * NOTE: not checking whether the symbols exist or not
 */

%{
  
(* Header (OCaml code) *)

open Term

let parse_error s = 
  print_endline s;
  flush stdout

let make_APP lst = 
  match lst with
  | [t] -> t
  | t1 :: body -> APP(t1, body)
  | [] -> failwith "Cannot make application with empty list."

%}

/* OCamlyacc declarations (names of terminal and non-terminal symbols, operator
   precedence, etc.)
*/

/* Terminal symbols */
%token <int> INDEX
%token <string> NAME STRING FORALL EXISTS VAR ABS NEW
%token IN MCTX ELIN EMP UNION ADDFORM REQIN REMOVED
%token LOLLI TIMES PLUS PIPE WITH TOP BOT ONE ZERO HBANG BANG QST NOT
%token COMMA LBRACKET RBRACKET LCURLY RCURLY LPAREN RPAREN UNDERSCORE DOT NEWLINE QUOTE
%right FORALL EXISTS
%left TIMES
%left PLUS
%left PIPE
%left WITH 
%left LOLLI
%right NOT NEW
%right QST BANG HBANG

/* Start symbol */
%start model
%type <Constraints.constraintpred list> model

/* GR TODO: remove the input things once I am using the parser only inside? */
/*%start input
%type <unit> input
*/

%% 

/* Grammar rules */

/*
input:
   empty   { }
  | NEWLINE { } 
  | model NEWLINE { $1 }
*/

model: 
  /* empty */                   { [] }
  | constraintPred              { [$1] }
  | constraintPred COMMA model  { $1 :: $3 }
  | LCURLY model RCURLY         { $2 }
;

constraintPred:
  | IN LPAREN QUOTE formula QUOTE COMMA contextVar RPAREN                           { Constraints.IN($4, $7) }
  | MCTX LPAREN QUOTE formula QUOTE COMMA contextVar RPAREN                         { Constraints.MCTX($4, $7) }
  | ELIN LPAREN QUOTE formula QUOTE COMMA contextVar RPAREN                         { Constraints.ELIN($4, $7) }
  | EMP LPAREN contextVar RPAREN                                                    { Constraints.EMP($3) }
  | UNION LPAREN contextVar COMMA contextVar COMMA contextVar RPAREN                { Constraints.UNION($3, $5, $7) }
  | ADDFORM LPAREN QUOTE formula QUOTE COMMA contextVar COMMA contextVar RPAREN     { Constraints.ADDFORM($4, $7, $9) }
  | REQIN LPAREN QUOTE formula QUOTE COMMA contextVar RPAREN                        { Constraints.REQIN($4, $7) }
  | REMOVED LPAREN QUOTE formula QUOTE COMMA contextVar COMMA contextVar RPAREN     { Constraints.REMOVED($4, $7, $9) }
  ;

contextVar: 
  | NAME UNDERSCORE INDEX { ($1, $3) }
;

formula:
  | pred  { $1 }
  | TOP   { TOP }
  | BOT   { BOT }
  | ONE   { ONE }
  | ZERO  { ZERO }
  | LBRACKET subexp RBRACKET BANG formula   { BANG ($2,$5) }
  | LBRACKET subexp RBRACKET HBANG formula  { HBANG ($2,$5) }
  | LBRACKET subexp RBRACKET QST formula    { QST ($2,$5) }
  | BANG formula             { BANG (CONS("$infty"),$2) }
  | HBANG formula            { HBANG (CONS("$infty"),$2) }
  | QST formula              { QST (CONS("$infty"),$2) }
  | FORALL formula           { FORALL ($1, 0, $2) } 
  | EXISTS formula           { EXISTS ($1, 0, $2) } 
  | formula TIMES formula    { TENSOR ($1, $3)}
  | formula PLUS formula     { ADDOR ($1, $3)}
  | formula PIPE formula     { PARR ($1, $3)}
  | formula WITH formula     { WITH ($1, $3)}
  /* a [s]-o b is stored as LOLLI(s, b, a) */
  | formula LBRACKET subexp RBRACKET LOLLI formula { LOLLI ($3, $6, $1)}
  | LPAREN formula RPAREN    { $2 }
  | NEW formula              { NEW ($1, $2) }
  | NOT formula              { nnf (NOT($2)) }
;

pred:
  | NAME         { PRED ($1, CONS($1), NEG) } 
  | NAME terms   { PRED ($1, APP(CONS($1), $2), NEG ) }
  | VAR          { VAR {str = $1; id = 0; tag = LOG; ts = 0; lts = 0} }
  | VAR terms { 
    let var_head =  VAR {str = $1; id = 0; tag = LOG; ts = 0; lts = 0} in
    APP(var_head, $2)
  }
;

terms:
  | term                        { [$1] }
  | term terms                  { $1 :: $2 }
  | ABS terms                   { [ABS($1, 0, (make_APP $2))] } 
  | LPAREN terms RPAREN         { [make_APP $2] }
  | LPAREN terms RPAREN terms   { (make_APP $2) :: $4 } 
;

term:
  | NAME     { CONS ($1) }
  | VAR      { VAR {str = $1; id = 0; tag = LOG; ts = 0; lts = 0} }  
  | STRING   { STRING ($1) }
;

subexp:
  | NAME { CONS ($1) }
;

%%

