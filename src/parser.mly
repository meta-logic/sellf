/* File parser_systems.mly 
 *
 * Parse specifications of sequent calculus systems, as described in "Extended
 * Framework for Specifying and Reasoning about Proof Systems" by Vivek Nigam,
 * Elaine Pimentel and Giselle Reis
*/
%{
open Context
open Types
open Prints
open TypeChecker
open Coherence
open Context
open Subexponentials
open Staticpermutationcheck

type ruleType = 
  | AXIOM
  | CUT
  | INTRO
  | STRUCT
  | NORULE

let rules = ref NORULE;;

let make_APP lst = 
  match lst with
  | [t] -> t
  | t1 :: body -> APP(t1, body)
  | [] -> failwith "Cannot make application with empty list."

let check_val_subexp sub1 sub2 = 
  match (Subexponentials.type_of sub1), (Subexponentials.type_of sub2) with
    | LIN, LIN -> true
    | LIN, AFF -> true
    | LIN, REL -> true
    | LIN, UNB -> true
    | AFF, UNB -> true
    | REL, UNB -> true
    | UNB, UNB -> true
    | _,_ -> false
;;

%}

%token KIND DOTS TINT TLIST DOT TYPE TARR PRED TSTRING PLUS MINUS TIMES DIV LESS LEQ GRT GEQ EQ NEQ DEF 
COMMA SEMICOLON PIPE TOP ONE CUT WITH LLIST RLIST LHEADTAIL INVLOLLI LPAREN RPAREN SUBEX TENSOR CONTEXT SUBEXPREL 
LBRACKET RBRACKET LCURLY RCURLY LOLLI BANG HBANG TSUBEX NEQ IS PRINT ON OFF HELP VERBOSE TIME EXIT LOAD
QST BOT ZERO POS NEG NOT RULES AXIOM CUTRULE INTRODUCTION STRUCTURAL SUBEXCTX HASH
%token <string> NAME STRING VAR FORALL EXISTS TSUB CTXTYPE ABS NEW FILE CONNTEX
%token <int> INT
%right ARR  
%left TIMES
%left PLUS
%left PIPE
%left WITH 
%left LOLLI
%right NOT NEW
%right FORALL EXISTS
%right QST BANG HBANG

%start types             /* the entry point */
%type <string option> types 
%type <types> typeN

%start clause            /* the entry point */
%type <string option> clause
%type <terms list> terms

%start goal             /* the entry point */
%type <string option> goal

%start top             /* the entry point */
%type <string> top 

%type <string list> conList

%%  

/* G: Saves the kinds and types declared in hash tables. */
types:
KIND NAME TYPE DOT { 
  let result = Specification.addKindTbl (TKIND ($2)) in
  match result with
    | None -> if !Term.verbose then begin 
      print_string (" New kind "^$2^" created.\n")
      end;
      None
    | Some (k) -> print_endline ("[ERROR] Kind already declared: "^$2);
      flush stdout; Some (k)
}
| TYPE NAME typeN CONNTEX DOT {
  let dupChk = Specification.isKindDeclared $2 in
  let dupChk2 = Specification.isTypeDeclared $2 in
  match dupChk, dupChk2 with
    | false, false -> Specification.addTypeTbl $2 $3; 
      Hashtbl.add Subexponentials.conTexTbl $2 $4;
      if !Term.verbose then begin
        print_endline (" New type created: "^$2^" : "^(typeToString $3));
        flush stdout;
      end;
      None
    | true, _ -> print_string ("[ERROR] Type previously declared as a kind: "^$2);
      print_newline(); flush stdout; Some ($2)
    | _, true -> print_string ("[ERROR] Type previously declared as a type: "^$2);
      print_newline(); flush stdout; Some($2) 
}
| TYPE NAME typeN DOT { 
  let dupChk = Specification.isKindDeclared $2 in
  let dupChk2 = Specification.isTypeDeclared $2 in
  match dupChk, dupChk2 with
    | false, false -> Specification.addTypeTbl $2 $3; 
      if !Term.verbose then begin
        print_endline (" New type created: "^$2^" : "^(typeToString $3));
        flush stdout;
      end;
      None
    | true, _ -> print_string ("[ERROR] Type previously declared as a kind: "^$2);
      print_newline(); flush stdout; Some ($2)
    | _, true -> print_string ("[ERROR] Type previously declared as a type: "^$2);
      print_newline(); flush stdout; Some($2) 
}
;

conList: 
NAME { [$1] }
| NAME SEMICOLON conList { $1 :: $3 }
;

/* G: Checks whether the types declared are valid and of existing kinds. */
typeN: 
NAME { match Specification.isKindDeclared $1 with 
  | false -> print_string ("[ERROR] Kind not declared: "^$1);
    print_newline(); flush stdout; 
    assert false
  | true -> if $1 = "o" then TBASIC (TPRED)
    else TBASIC (TKIND ($1)) 
}
| TINT                           { TBASIC (TINT) }
| TSTRING                        { TBASIC (TSTRING) }
| TSUBEX                          {TBASIC (TSUBEX) }
| typeN TARR typeN               { ARR ($1, $3) }
| LPAREN typeN RPAREN            { $2 }
| LPAREN TLIST TINT RPAREN       { TBASIC (TLIST (TINT)) } /* G: list of int and list of string. Declare the other types of lists? */
| LPAREN TLIST TSTRING RPAREN    { TBASIC (TLIST (TSTRING)) }
;

clause: 
/*VN: Creates a new subexponential into the hash table with the subexponential types.*/
| SUBEX NAME TSUB DOT { 
  match Subexponentials.isSubexponentialDeclared $2 with
    | false -> begin
      match $3 with 
        | "lin" ->
          initSubexp $2;
          Subexponentials.addType $2 LIN;
          if !Term.verbose then print_endline ("New linear subexponential: "^$2);
          None
        | "aff" -> 
          initSubexp $2;
          Subexponentials.addType $2 AFF;
          if !Term.verbose then print_endline ("New affine subexponential: "^$2);
          None
        | "rel" -> 
          initSubexp $2;
          Subexponentials.addType $2 REL;
          if !Term.verbose then print_endline ("New relevant subexponential: "^$2);
          None
        | "unb" -> 
          initSubexp $2;
          Subexponentials.addType $2 UNB;
          if !Term.verbose then print_endline ("New unbounded subexponential: "^$2);
          None
        | str -> failwith ("[ERROR] "^str^" is not a valid subexponential type. Use 'lin', 'aff', 'rel' or 'unb'.")
    end
    | true -> failwith ("Subexponential name previously declared: "^$2)
}

/*VN: Creates a new odering among subexponential names.*/
| SUBEXPREL NAME LESS NAME DOT { 
  match (Subexponentials.isSubexponentialDeclared $2), (Subexponentials.isSubexponentialDeclared $4) with
    | true, true -> 
      if check_val_subexp $2 $4 then
        (Hashtbl.add Subexponentials.orderTbl $2 $4; None) 
      else failwith ("ERROR: More powerful subexponential "^$2^" cannot be smaller than the less powerful subexponential "^$4)
    | false, _ -> failwith ("ERROR: Subexponential name not declared: "^$2) 
    | _, false -> failwith ("ERROR: Subexponential name not declared: "^$4) 
}
| SUBEXPREL NAME GEQ NAME DOT {
  match (Subexponentials.isSubexponentialDeclared $2), (Subexponentials.isSubexponentialDeclared $4) with
    | true, true -> 
      if check_val_subexp $4 $2 then
        (Hashtbl.add Subexponentials.orderTbl $4 $2; None) 
      else failwith ("ERROR: More powerful subexponential "^$4^" cannot be smaller than the less powerful subexponential "^$2)
    | false, _ -> failwith ("ERROR: Subexponential name not declared: "^$2) 
    | _, false -> failwith ("ERROR: Subexponential name not declared: "^$4) 
}

/* Define the context type */
| SUBEXCTX NAME CTXTYPE NAME DOT {
  match (Subexponentials.isSubexponentialDeclared $2) with
    | true -> 
      let arity = match $3 with
        | "single" -> SINGLE
        | "many" -> MANY
        | _ -> failwith ("ERROR: Subexpctx invalid arity: "^$3)
      in
      let side = match $4 with 
        | "lft" -> LEFT
        | "rght" -> RIGHT
        | "rghtlft" -> RIGHTLEFT
        | _ -> failwith ("ERROR: Subexpctx invalid side: "^$4)
      in
      Hashtbl.add Subexponentials.ctxTbl $2 (arity, side); None
    | false -> failwith ("ERROR: Subexponential name not declared: "^$2) 
}
| SUBEXCTX NAME CTXTYPE NAME LBRACKET conList RBRACKET DOT {
  match (Subexponentials.isSubexponentialDeclared $2) with
    | true -> 
      let arity = match $3 with
        | "single" -> SINGLE
        | "many" -> MANY
        | _ -> failwith ("ERROR: Subexpctx invalid arity: "^$3)
      in
      let side = match $4 with 
        | "lft" -> LEFT
        | "rght" -> RIGHT
        | "rghtlft" -> RIGHTLEFT
        | _ -> failwith ("ERROR: Subexpctx invalid side: "^$4)
      in
      List.iter (fun con ->
	let conList' = try Hashtbl.find Subexponentials.conTbl $2 with Not_found -> [] in
	Hashtbl.replace Subexponentials.conTbl $2 (con :: conList')
      ) $6;
      Hashtbl.add Subexponentials.ctxTbl $2 (arity, side); None
    | false -> failwith ("ERROR: Subexponential name not declared: "^$2) 
}

/* Defines which kind of rules we are specifying now */
| RULES AXIOM DOT { rules := AXIOM; None }
| RULES CUTRULE DOT { rules := CUT; None }
| RULES INTRODUCTION DOT { rules := INTRO; None }
| RULES STRUCTURAL DOT { rules := STRUCT; None }

/* System's specifications must have this form. */
| body DOT {
  let clause_typecheck = deBruijn false $1 in
  let _ = typeCheck clause_typecheck in
  let clause = deBruijn true $1 in

  (match !rules with
    | AXIOM ->
      (* For coherence *)
      Specification.addAxiom clause
    | CUT -> 
      (* For principal cut and coherence *)
      Specification.addCutRule clause
    | INTRO ->
      (* For coherence *)
      Specification.processIntroRule $1;
      (* For principal cut *)
      Specification.addIntroRule clause
    | STRUCT ->
      (* For principal cut *)
      Specification.addStructRule clause 
    | NORULE -> Specification.addOthers clause
  );

  if !Term.verbose then begin
    print_endline ("New formula: "^(termToString clause));
    flush stdout
  end;
  None
}
;

/* G: goal is always a single formula (check if I can use body here). 
 * Using types clause and goal so that it can typecheck the expression.
 */
goal:
body DOT {
  let raw_clause = (CLS (DEF,TOP, $1)) in 
  let clause_typecheck = deBruijn false raw_clause in
  let _ = typeCheck clause_typecheck in
  let clause = deBruijn true $1 in
  
  Term.goal := clause;
  if !Term.verbose then begin
    print_endline (" New goal: "^(termToString $1));
    flush stdout
  end;
  None
}
;

/* G: parses the body of a clause.
 * The first option is for constants and the second 
 * one for functions.
 */
prop:
| NAME { 
  match (Specification.isTypeDeclared $1), (Subexponentials.isSubexponentialDeclared $1) with
    | false, false -> print_string ("[ERROR] Constant not declared -> "^$1);
      print_newline(); flush stdout; assert false
      (*PRED ($1, CONST($1), NEG )*)
    | true, _ -> PRED ($1, CONST($1), NEG )
    (* GR Parsing subexponentials as predicates? *)
    | _, true -> PRED ($1, CONST($1), NEG )
}
| NAME terms {
  match (Specification.isTypeDeclared $1), (Subexponentials.isSubexponentialDeclared $1) with
    | false, false -> print_string ("[ERROR] Constant not declared -> "^$1);
      print_newline(); flush stdout; assert false
      (*PRED ($1, CONST($1), NEG )*)
    | true, _ -> PRED ($1, APP(CONST($1), $2), NEG )
    | _, true -> PRED ($1, CONST($1), NEG )
}

/* VN: Predicates can also be variables. */
| VAR { 
  let var_head = VAR {str = $1; id = 0; tag = LOG; ts = 0; lts = 0} in 
  var_head
}
| VAR terms { 
  let var_head =  VAR {str = $1; id = 0; tag = LOG; ts = 0; lts = 0} in
  APP(var_head, $2)
}
;

body:
| prop                  { $1 }
| logCst                { $1 }
| LBRACKET term RBRACKET BANG body              {BANG ($2,$5)}
| LBRACKET term RBRACKET HBANG body             {HBANG ($2,$5)}
| LBRACKET term RBRACKET QST body               {QST ($2,$5)}
| BANG body             { BANG (CONST("$infty"),$2) }
| HBANG body            { HBANG (CONST("$infty"),$2) }
| QST body              { QST (CONST("$infty"),$2) }
| FORALL body           { FORALL ($1, 0, $2) } 
| EXISTS body           { EXISTS ($1, 0, $2) } 
| ABS body              { ABS($1, 0, $2) }
| body TIMES body       { TENSOR ($1, $3)}
| body PLUS body        { ADDOR ($1, $3)}
| body PIPE body        { PARR ($1, $3)}
| body WITH body        { WITH ($1, $3)}
/* a [s]-o b is stored as LOLLI(s, b, a) */
| body LBRACKET term RBRACKET LOLLI body       { LOLLI ($3, $6, $1)}
| LPAREN body RPAREN    { $2 }
| NEW body              { NEW ($1, $2) }
| LCURLY body RCURLY    { BRACKET($2) }
| NOT body              { Term.nnf (NOT($2)) }
;

terms:
| term                        { [$1] }
| term terms                  { $1 :: $2 }
| LPAREN terms RPAREN         { [make_APP $2] }
| LPAREN terms RPAREN terms   { (make_APP $2) :: $4 } 
;

term:
| NAME { 
  match (Specification.isTypeDeclared $1), (Subexponentials.isSubexponentialDeclared $1) with
    | false, false -> print_string ("[ERROR] Constant not declared -> "^$1);
      print_newline(); flush stdout; assert false
      (*PRED ($1, CONST($1), NEG )*)
    | true, _ -> CONST ($1)
    | _, true -> CONST ($1)
}
| VAR               { VAR {str = $1; id = 0; tag = LOG; ts = 0; lts = 0} }  
| INT               { INT ($1) } 
| STRING            { STRING ($1) }

logCst:
| TOP  {TOP}
| ONE  {ONE}
| BOT  {BOT}
| ZERO {ZERO}
;

top: 
| HELP    { 
  print_endline "\nThe following commands are available during state ':>':\n";
  print_endline "#load location-of-file (without extensions .sig nor .pl): loads \
    the corresponding program (the location is relative to the place the \
    executable file was launched);";
  print_endline "#verbose on or #verbose off: turns on or off the printing of \
    some steps of the computation. The default value is 'off';";
  (*print_endline "#time on or #time off: turns on or off the measuring of the
  execution time of a query. The default value is 'off'. (Note that the time
  measurement of the permutation checking is always on);";*)
  print_endline "#exit command terminates the program.";
  print_endline "#help displays this message.";
  
  print_endline "\nThe following commands are available during state '?>':";
  
  print_endline "\n** Helper commands **";
  print_endline "#check_rules: checks if all the rules of a file are bipoles.";
  print_endline "#scopebang: prints which subexponentials will have their \
    formulas erased and which should be empty when a !s formula is going to be \
    used.";
  print_endline "#done: you must type this to indicate that you are done working \
    with a file and before loading another one.\n";
  
  print_endline "\n** Quati commands **";
  print_endline "#rule: prints the selected object logic rule to a LaTeX file.";
  print_endline "#rules: prints all object logic rules to a LaTeX file.";
  print_endline "#bipole: prints the bipole of the selected rule to a LaTeX file";
  print_endline "#bipoles: prints the bipoles of all rules to a LaTeX file.";
  print_endline "#permute: checks if two rules of your choice permute.";
  print_endline "#permute_all: checks the permutation of all rules of the system.";
  print_endline "#permutation_graph: generates a permutation graph of all rules of the system.";

  print_endline "\n** Tatu commands **";
  print_endline "#principalcut: checks if the rules can permute until the cut becomes principal.";
  print_endline "#cutcoherence: checks whether the system specified on the file loaded is cut-coherent.";
  print_endline "#initialcoherence: checks whether the system specified on the file loaded is initial-coherent.";
  print_endline "#atomicelim: checks whether the system specified on the file loaded is weak coherent.";
  
  "help"
}
| VERBOSE ON {"verbose-on"}
| VERBOSE OFF {"verbose-off"}
| TIME ON {"time-on"}
| TIME OFF {"time-off"}
| EXIT                    {print_endline "Thank you for using SELLF."; exit 1}
| LOAD  FILE  {$2}

