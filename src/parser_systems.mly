/* File parser_systems.mly 
 *
 * Parse specifications of sequent calculus systems, as described in "Extended
 * Framework for Specifying and Reasoning about Proof Systems" by Vivek Nigam,
 * Elaine Pimentel and Giselle Reis
*/
%{
open Term
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
  match (Hashtbl.find subexTpTbl sub1), (Hashtbl.find subexTpTbl sub2) with
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
QST BOT ZERO POS NEG NOT RULES AXIOM CUTRULE INTRODUCTION STRUCTURAL
%token <string> NAME STRING VAR FORALL EXISTS TSUB ABS NEW FILE
%token <int> INT
%right ARR  
%left TIMES
%left PLUS
%left PIPE
%left WITH 
%left LOLLI
%start types             /* the entry point */
%type <string Term.option> types 
%type <Term.types> typeN
%start clause            /* the entry point */
%type <string Term.option> clause
%type <Term.terms list> terms
%start top             /* the entry point */
%type <string> top 
%%  

/* G: Saves the kinds and types declared in hash tables. */
types:
KIND NAME TYPE DOT { 
  let result = addKindTbl (TKIND ($2)) in
  match result with
    | NONE -> if !verbose then begin 
      print_string (" New kind "^$2^" created.\n")
      end;
      NONE
    | SOME (k) -> print_endline ("[ERROR] Kind already declared: "^$2);
      flush stdout; SOME (k)
}
| TYPE NAME typeN DOT { 
  let dupChk = notInTbl kindTbl $2 in 
  match dupChk with
    | NONE -> 
      let dupChk2 =  notInTbl typeTbl $2 in 
      begin
        match dupChk2 with
          | NONE -> addTypeTbl $2 $3; 
            if !verbose then begin
              print_endline (" New type created: "^$2^" : "^(typeToString $3));
              flush stdout;
            end;
            NONE
          | SOME (k) -> print_string ("[ERROR] Type previously declared as a type: "^$2);
            print_newline(); flush stdout; 
            SOME (k) 
      end
    | SOME (k)-> print_string ("[ERROR] Type previously declared as a kind: "^$2);
      print_newline(); flush stdout; SOME (k)
}
;

/* G: Checks whether the types declared are valid and of existing kinds. */
typeN: 
NAME { match  notInTbl kindTbl $1 with 
  | NONE -> print_string ("[ERROR] Kind not declared: "^$1);
    print_newline(); flush stdout; 
    assert false
  | SOME (_) -> if $1 = "o" then TBASIC (TPRED)
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


/* G: Saves the clauses in a hash table */
clause: 
/*VN: Creates a new subexponential into the hast table with the subexponential types.*/
| SUBEX NAME TSUB DOT { 
  match notInTbl subexTpTbl $2 with
    | NONE -> begin
      match $3 with 
        | "lin" ->
          initSubexp $2;
          addType $2 LIN;
          if !verbose then print_endline ("New linear subexponential: "^$2);
          NONE
        | "aff" -> 
          initSubexp $2;
          addType $2 AFF;
          if !verbose then print_endline ("New affine subexponential: "^$2);
          NONE
        | "rel" -> 
          initSubexp $2;
          addType $2 REL;
          if !verbose then print_endline ("New relevant subexponential: "^$2);
          NONE
        | "unb" -> 
          initSubexp $2;
          addType $2 UNB;
          if !verbose then print_endline ("New unbounded subexponential: "^$2);
          NONE
        | str -> failwith ("[ERROR] "^str^" is not a valid subexponential type. Use 'lin', 'aff', 'rel' or 'unb'.")
    end
    | SOME (_) -> failwith ("Subexponential name previously declared: "^$2)
}

/*VN: Creates a new odering among subexponential names.*/
| SUBEXPREL NAME LESS NAME DOT { 
  match (notInTbl subexTpTbl $2), (notInTbl subexTpTbl $4) with
    | SOME(_),SOME(_) -> 
      if check_val_subexp $2 $4 then
        (Hashtbl.add subexOrdTbl $2 $4; NONE) 
      else failwith ("ERROR: More powerful subexponential "^$2^" cannot be smaller than the less powerful subexponential "^$4)
    | NONE,_ -> failwith ("ERROR: Subexponential name not declared: "^$2) 
    | _, NONE -> failwith ("ERROR: Subexponential name not declared: "^$4) 
}
| SUBEXPREL NAME GEQ NAME DOT {
  match (notInTbl subexTpTbl $2), (notInTbl subexTpTbl $4) with
    | SOME(_),SOME(_) -> 
      if check_val_subexp $4 $2 then
        (Hashtbl.add subexOrdTbl $4 $2; NONE) 
      else failwith ("ERROR: More powerful subexponential "^$4^" cannot be smaller than the less powerful subexponential "^$2)
    | NONE,_ -> failwith ("ERROR: Subexponential name not declared: "^$2) 
    | _, NONE -> failwith ("ERROR: Subexponential name not declared: "^$4) 
}

/* Defines which kind of rules we are specifying now */
| RULES AXIOM DOT { rules := AXIOM; NONE }
| RULES CUTRULE DOT { rules := CUT; NONE }
| RULES INTRODUCTION DOT { rules := INTRO; NONE }
| RULES STRUCTURAL DOT { rules := STRUCT; NONE }

/* System's specifications must have this form. */
| body DOT {
  let clause_typecheck = deBruijn false $1 in
  let _ = typeCheck clause_typecheck in
  let clause = deBruijn true $1 in

  (match !rules with
    | AXIOM -> () (* Will we need the axiom?? *)
    | CUT -> 
      (* For coherence *)
      store clause "$infty";
      (* For principal cut *)
      addCutRule clause
    | INTRO ->
      (* For coherence *)
      addIntrodRule $1
    | STRUCT ->
      (* For principal cut *)
      addStructRule clause 
    | NORULE -> failwith "Rule type not specified."
  );

  if !verbose then begin
    print_endline ("New formula: "^(termToString clause));
    flush stdout
  end;
  NONE
}
;

/* G: parses the body of a clause.
 * The first option is for constants and the second 
 * one for functions.
 * TODO: change this so it accepts more complex expressions on the left-hand side
 */
prop:
| NAME { 
  match (notInTbl typeTbl $1), (notInTbl subexTpTbl $1) with
    | NONE, NONE -> print_string ("[ERROR] Constant not declared -> "^$1);
      print_newline(); flush stdout; 
      (*PRED ($1, CONS($1), (getAtomPol $1) )*)
      PRED ($1, CONS($1), NEG )
    | SOME (k), _ -> (*PRED ($1, CONS($1), (getAtomPol $1) )*) 
      PRED ($1, CONS($1), NEG )
    | _, SOME (k) -> (*PRED ($1, CONS($1), (getAtomPol $1) )*)
      PRED ($1, CONS($1), NEG )
}
| NAME terms {
  match (notInTbl typeTbl $1), (notInTbl subexTpTbl $1) with
    | NONE, NONE -> print_string ("[ERROR] Constant not declared -> "^$1);
      print_newline(); flush stdout; 
      (*PRED ($1,CONS($1), (getAtomPol $1) )*)
      PRED ($1, CONS($1), NEG )
    | SOME (k), _ ->  (*PRED($1, APP(CONS($1), $2), (getAtomPol $1) )*)
      PRED ($1, APP(CONS($1), $2), NEG )
    | _, SOME (k) -> (*PRED ($1, CONS($1), (getAtomPol $1) )*)
      PRED ($1, CONS($1), NEG )
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
| FORALL body           { FORALL ($1, 0, $2) } 
| EXISTS body           { EXISTS ($1, 0, $2) } 
| body TIMES body       { TENSOR ($1, $3)}
| body PLUS body        { ADDOR ($1, $3)}
| body PIPE body        { PARR ($1, $3)}
| body WITH body        { WITH ($1, $3)}
/* a [s]-o b is stored as LOLLI(s, b, a) */
| body LBRACKET term RBRACKET LOLLI body       { LOLLI ($3, $6, $1)}
| LPAREN body RPAREN    { $2 }
| NEW body              { NEW ($1, $2) }
| LCURLY body RCURLY    {BRACKET($2)}
| NOT body              {Term.deMorgan (NOT($2)) }
;

terms:
| term                        { [$1] }
| term terms                  { $1 :: $2 }
| ABS terms                   {[ABS($1, 0, (make_APP $2))]}
| LPAREN terms RPAREN         { [make_APP $2] }
| LPAREN terms RPAREN terms   { (make_APP $2) :: $4 } 
;

term:
| NAME { 
  match (notInTbl typeTbl $1), (notInTbl subexTpTbl $1) with
    | NONE, NONE -> print_string ("[ERROR] Constant not declared -> "^$1);
      print_newline(); flush stdout; 
      PRED ($1, CONS($1), NEG )
    | SOME (k), _ -> CONS ($1)
    | _, SOME (k) -> CONS ($1)
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
  print_endline "There are the following commands available during state ':>':\n";
  print_endline "#load location-of-file (without extensions .sig nor .pl): loads the corresponding program (the location is relative to the place the executable file was launched);";
  print_endline "#verbose on or #verbose off: turns on or off the printing of some steps of the computation. The default value is 'off';";
  (*print_endline "#time on or #time off: turns on or off the measuring of the
  execution time of a query. The default value is 'off'. (Note that the time
  measurement of the permutation checking is always on);";*)
  print_endline "#exit command terminates the program.";
  print_endline "#help displays this message;";
  print_endline "There are the following commands available during state '?>':\n";
  (*print_endline "#perm: checks if the rules specified in the file permute (all
  possible combinations of 2 rules).";*)
  (*print_endline "#macro: generates the macro rules of each rule of the file
  loaded.";*)
  print_endline "#principalcut: checks if the rules can permute until the cut becomes principal.";
  print_endline "#coherence: checks is the system specified on the file loaded is coherent.";
  print_endline "#scopebang: prints which subexponentials will have their formulas erased and which should be empty when a !s formula is going to be used.";
  print_endline "#done: you must type this to indicate that you are done working with a file and before loading another one.";
  "help"
}
| VERBOSE ON {"verbose-on"}
| VERBOSE OFF {"verbose-off"}
| TIME ON {"time-on"}
| TIME OFF {"time-off"}
| EXIT                    {print_endline "Thank you for using SELLF."; exit 1}
| LOAD  FILE  {$2}

