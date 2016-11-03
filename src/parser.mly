/* 
 * File parser.mly 
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

%token KIND TYPE TSUBEX SUBEX SUBEXCTX CONTEXT SUBEXPREL POS NEG
       RULES AXIOM CUTRULE STRUCTURAL INTRODUCTION
       LOAD HELP VERBOSE TIME ON OFF EXIT
       TINT TLIST TSTRING
       TARR DOT LPAREN RPAREN LBRACKET RBRACKET LCURLY RCURLY LESS GEQ SEMICOLON
       TOP BOT ONE ZERO BANG QST FORALL EXISTS TIMES PLUS PIPE WITH LOLLI NOT INVLOLLI
%token <string> CONNTEX CTXTYPE CTXSIDE TSUB NAME VAR LOAD
%token <int> INT
%right ARR  
/* Precedence rules
 * 1. All symbols in the same line are given the same precedence
 * 2. Precedence is increasing with the line number.
 */
%right INVLOLLI
%right LOLLI
%right TIMES
%right PLUS
%right PIPE
%right WITH 
%nonassoc NOT FORALL EXISTS BANG QST LBRACKET RBRACKET

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
/* Lists of integers and strings */
| LPAREN TLIST TINT RPAREN       { TBASIC (TLIST (TINT)) }
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
| SUBEXCTX NAME CTXTYPE CTXSIDE DOT {
  match (Subexponentials.isSubexponentialDeclared $2) with
    | true -> 
      let arity = match $3 with
        | "single" -> SINGLE
        | "many" -> MANY
        | _ -> failwith ("ERROR: Subexpctx invalid arity: "^$3)
      in
      let side = match $4 with 
        | "ant" -> LEFT
        | "suc" -> RIGHT
        | "antsuc" -> RIGHTLEFT
        | _ -> failwith ("ERROR: Subexpctx invalid side: "^$4)
      in
      Hashtbl.add Subexponentials.ctxTbl $2 (arity, side); None
    | false -> failwith ("ERROR: Subexponential name not declared: "^$2) 
}
| SUBEXCTX NAME CTXTYPE CTXSIDE LBRACKET conList RBRACKET DOT {
  match (Subexponentials.isSubexponentialDeclared $2) with
    | true -> 
      let arity = match $3 with
        | "single" -> SINGLE
        | "many" -> MANY
        | _ -> failwith ("ERROR: Subexpctx invalid arity: "^$3)
      in
      let side = match $4 with 
        | "ant" -> LEFT
        | "suc" -> RIGHT
        | "antsuc" -> RIGHTLEFT
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
  /* (F) */
  | LPAREN body RPAREN    { $2 }
  /* propositional variable */
  | prop    { $1 }
  /* T, 1, bot, 0 */
  | logCst  { $1 }
  /* !^l F : ![l] F */
  | BANG LBRACKET term RBRACKET body  {BANG ($3,$5)}
  /* ?^l F : ?[l] F */
  | QST LBRACKET term RBRACKET body   {QST ($3,$5)}
  /* !^infty F : ! F */
  | BANG body             { BANG (CONST("infty"),$2) }
  /* ?^infty F : ? F */
  | QST body              { QST (CONST("infty"),$2) }
  /* F^{perp} : not F (the formula is already stored in NNF) */
  | NOT body              { Term.nnf (NOT($2)) }
  /* ∀ x. F : all x F */
  | FORALL VAR body       { FORALL ($2, 0, $3) } 
  /* ∃ x. F : exs x F */
  | EXISTS VAR body       { EXISTS ($2, 0, $3) } 
  /* A & B : A & B */
  | body WITH body        { WITH ($1, $3)}
  /* A ⅋ B : A | B */
  | body PIPE body        { PARR ($1, $3)}
  /* A ⊕ B : A + B */
  | body PLUS body        { ADDOR ($1, $3)}
  /* A ⊗ B : A * B */
  | body TIMES body       { TENSOR ($1, $3)}
  /* A -o B : A -o B*/
  | body LOLLI body       { LOLLI (CONST("gamma"), $3, $1) }
  /* For horn-clause-like definitions (we make no restrictions) */
  | body INVLOLLI body    { LOLLI (CONST("gamma"), $1, $3) }
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
/* There was a string match here. Maybe this will create some problems? */
;

logCst:
| TOP  { TOP }
| ONE  { ONE }
| BOT  { BOT }
| ZERO { ZERO }
;

top: 
| HELP        { "help" }
| VERBOSE ON  { "verbose-on" }
| VERBOSE OFF { "verbose-off" }
| TIME ON     { "time-on" }
| TIME OFF    { "time-off" }
| EXIT        { "exit" }
| LOAD        { $1 }

