    /* File parser.mly */
%{
open Term
open Prints
(*open Structs*)
open TypeChecker
open Coherence
open Context
open Subexponentials

let currentctx = ref "$gamma" 

let rec curry term = 
  let rec curryAux termC termU = begin
    match termU with 
      | APP (termU1, [termU2]) -> 
        curryAux (APP (termC, [curry termU1])) termU2
      | x -> APP(termC, [x])
  end
  in
  match term with
    | APP (term1, [term2]) -> let term1C = curry term1 in 
      curryAux term1C term2             
    | x -> x

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

let rec cls_2_lolli form subexp = match form with
  | ABS(s, i, t) -> ABS(s, i, (cls_2_lolli t subexp))
  | CLS(ct, head, body) -> LOLLI(subexp, head, body)
  | _ -> failwith "No clause inside abstraction."
;;

let rec spec_2_form spec = match spec with
  | ABS(s, i, t) -> ABS(s, i, (spec_2_form t))
  | CLS(ct, head, body) -> TENSOR(NOT(head), body)
  (*| CLS(ct, head, body) -> body*)
  | _ -> failwith "No clause inside abstraction."
;;
%}

%token KIND DOTS TINT TLIST DOT TYPE TARR PRED TSTRING PLUS MINUS TIMES DIV LESS LEQ GRT GEQ EQ NEQ DEF 
COMMA SEMICOLON PIPE TOP ONE CUT WITH LLIST RLIST LHEADTAIL INVLOLLI LPAREN RPAREN SUBEX TENSOR CONTEXT SUBEXPREL 
LBRACKET RBRACKET LCURLY RCURLY LOLLI BANG HBANG TSUBEX NEQ IS PRINT ON OFF HELP VERBOSE TIME EXIT LOAD
QST BOT ZERO POS NEG NOT
%token <string> NAME STRING VAR FORALL EXISTS TSUB ABS NEW FILE
%token <int> INT
%right ARR  
%left COMMA
%left SEMICOLON
%left PIPE
%left WITH 
%left LOLLI
%left PLUS MINUS        /* lowest precedence */
%left TIMES DIV         /* medium precedence */
%start types             /* the entry point */
%type <string Term.option> types 
%type <Term.types> typeN
%start clause            /* the entry point */
%type <string Term.option> clause
%type <Term.terms> prop
%type <Term.terms list> terms
%type <Term.terms> intBody
%start goal             /* the entry point */
%type <string Term.option> goal
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
              print_string (" New type created: "^$2^" : ");
              print_type $3;
              print_newline (); flush stdout;
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
| SUBEXPREL NAME LEQ NAME DOT { 
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

/* TODO Parsing atom's polarity
| POS NAME DOT {
  addAtomPol $2 POS; NONE 
}
| NEG NAME DOT {
  addAtomPol $2 NEG; NONE
}
*/

/* VN: Marks that all formulas appearing after a context keyword are to be stored in the subexponential NAME.*/
| CONTEXT NAME DOT {  
  match notInTbl subexTpTbl $2 with
    | NONE ->  failwith ("ERROR: No such subexponential declared: "^$2)
    | SOME (_) ->  currentctx := $2; NONE
}

/* G: TODO: do not transform propositions in clauses */
| prop DOT { 
  match $1 with
    | PRED (p,ts,pol) -> 
      let raw_clause = (CLS (DEF,$1, ONE)) in
      let clause_typecheck = deBruijn false raw_clause in
      let _ = typeCheck clause_typecheck in
      let clause = deBruijn true raw_clause in
      begin
        match clause with 
          | ABS (s, i, t) ->
            (*Hashtbl.add rTbl p clause;*)
            let lolli = cls_2_lolli (ABS(s, i, t)) (CONS(!currentctx)) in
            (*add_cls lolli;*)
            store lolli !currentctx;
            (*rules := lolli :: !rules;*)
            if !verbose then begin
              print_string (" New clause: ");
              print_term lolli;
              print_newline();
              flush stdout
            end;
            NONE
          | CLS(DEF, head, ONE) -> 
            (*Hashtbl.add rTbl p clause;*)
            (*add_cls (LOLLI(CONS(!currentctx), head, ONE));*)
            store (LOLLI(CONS(!currentctx), head, ONE)) !currentctx;
            (*rules := (LOLLI(CONS(!currentctx), head, ONE)) :: !rules;*)
            if !verbose then begin
              print_string " New clause: ";
              print_term (LOLLI(CONS(!currentctx), head, ONE));
              print_newline ();
              flush stdout
            end;
            NONE
          | c -> 
            print_term c; print_newline (); 
            failwith "Impossible error while parsing prop DOT."
      end
    | _ -> NONE
}

| prop INVLOLLI body DOT { 
  match $1 with 
    | PRED (p,ts,pol) -> 
      let raw_clause = (CLS (DEF, $1, $3)) in
      let clause_typecheck = deBruijn false raw_clause in
      let _ = typeCheck clause_typecheck in
      let clause = deBruijn true raw_clause in
      begin
        match clause with 
          | ABS(_, _, _)
          | CLS(DEF, _, _) -> (* Clause with no variables *) 
            (*Hashtbl.add rTbl p (clause); *)
            let lolli = cls_2_lolli clause (CONS(!currentctx)) in
            (*add_cls lolli;*)
            store lolli !currentctx;
            (* For macro-rules *)
            (*rules :=  lolli :: !rules;*)
            
            if !verbose then begin
              print_string (" New clause: ");
              print_term lolli;
              print_newline();
              flush stdout
            end;
            NONE
          | _ -> failwith "Impossible error while parsing."
      end
    | _ -> NONE 
}

/* G: DEF is used for specification of systems */
| prop DEF body DOT { 
  let raw_clause = (CLS (DEF, $1, $3)) in
  let clause_typecheck = deBruijn false raw_clause in
  let _ = typeCheck clause_typecheck in
  let clause = deBruijn true raw_clause in
  begin
    match clause with 
      | ABS(_, _, _)
      | CLS(DEF, _, _) -> 
        (* NOTE: transforms the clause into a formula ((not A) x B) *)
        let f = spec_2_form clause in
        
        (* For macro-rules *)
        (*rules :=  f :: !rules;*)
        (* For coherence *)
        addSpec f;

        if !verbose then begin
          print_string (" New clause: ");
          print_term f;
          print_newline();
          flush stdout
        end;
        NONE
      | _ -> failwith "Impossible error while parsing."
  end
}

/* Initial and cut specifications must have this form. */
| body DOT {
  let clause_typecheck = deBruijn false $1 in
  let _ = typeCheck clause_typecheck in
  let clause = deBruijn true $1 in
  
  (* For macro-rules *)
  (*rules := clause :: !rules;*)
  (* For coherence *)
  store clause "$infty";

  if !verbose then begin
    print_string (" New clause: ");
    print_term clause;
    print_newline();
    flush stdout
  end;
  NONE
}
;

/* G: goal is always a single formula (check if I can use body here). Saved in a list. 
 * Using types clause and goal so that it can typecheck the expression.
 */
goal:
body DOT {
  let raw_clause = (CLS (DEF,TOP, $1)) in 
  let clause_typecheck = deBruijn false raw_clause in
  let _ = typeCheck clause_typecheck in
  let clause = deBruijn true $1 in
  let clause_goal = Boundedproofsearch.apply_ptr clause in
  (* TODO store this somewhere *)
 (* add_goals clause_goal;*)
  if !verbose then begin
    print_string (" New goal: ");
    print_term $1;
    print_newline();
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
| intComp               { $1 }
| intAssign           {$1}
| print_term          {$1}
/*| equality              { $1 } */
| logCst                { $1 }
| CUT                   { CUT }
| LBRACKET term RBRACKET BANG body              {BANG ($2,$5)}
| LBRACKET term RBRACKET HBANG body             {HBANG ($2,$5)}
| LBRACKET term RBRACKET QST body               {QST ($2,$5)}
| FORALL body           { FORALL ($1, 0, $2) } 
| EXISTS body           { EXISTS ($1, 0, $2) } 
| body COMMA body       { TENSOR ($1, $3)}
| body SEMICOLON body   { ADDOR ($1, $3)}
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
| term terms                  { $1 :: $2
    (*match $2 with
     | APP(t1, t2) -> let lst = List.append [t1] t2 in APP($1, lst)
     | _ -> APP($1, [$2]) *) }
    | ABS terms                {[ABS($1, 0, (make_APP $2))]}
    | LPAREN terms RPAREN         { [make_APP $2] }
    | LPAREN terms RPAREN terms   { (make_APP $2) :: $4
        (* match $4 with 
         | APP (t1, t2) -> let lst = List.append [t1] t2 in 
         APP($2,lst)
         | _ -> APP ($2, [$4]) *)} 
        ;

term:
| NAME { match (notInTbl typeTbl $1), (notInTbl subexTpTbl $1) with
    | NONE, NONE -> print_string ("[ERROR] Constant not declared -> "^$1);
      print_newline(); flush stdout; 
      (*PRED ($1, CONS($1), (getAtomPol $1) )*)
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

intComp:
| intBody EQ intBody     {COMP (EQ,$1, $3)}
| intBody LESS intBody   {COMP (LESS,$1, $3)} 
| intBody GEQ intBody    {COMP (GEQ,$1, $3)}
| intBody GRT intBody    {COMP (GRT,$1, $3)}
| intBody LEQ intBody    {COMP (LEQ,$1, $3)}
| intBody NEQ intBody    {COMP (NEQ,$1, $3)}
;

intAssign:
| VAR IS intBody       {ASGN (VAR {str = $1; id = 0; tag = LOG; ts = 0; lts = 0}, $3) }

print_term:
| PRINT terms           {PRINT (make_APP $2)}

intBody: 
| INT                   {INT ($1)}
| VAR                   {VAR {str = $1; id = 0; tag = LOG; ts = 0; lts = 0}}
| intBody PLUS intBody  {PLUS ($1,$3)}
| intBody MINUS intBody {MINUS ($1,$3)} 
| intBody TIMES intBody {TIMES ($1,$3)}
| intBody DIV intBody   {DIV ($1,$3)}
| LPAREN intBody RPAREN {$2}
;

/* equality:
 *| VAR EQ terms {match $3 with
 *                          | [t] -> EQU ($1, 0, t)
 *                          | _ -> failwith "ERROR: Right-side of equality contains too many terms."}
 * ; */

top: 
| HELP    { 
  (* TODO: maybe we should start distinguishing which commands are to be typed after a file was loaded 
   * (file dependant) and which can be typed at the top level. *)
  print_endline "There are the following commands available during state ':>':\n";
  print_endline "#load location-of-file (without extensions .sig nor .pl): loads the corresponding program (the location is relative to the place the executable file was launched);";
  print_endline "#verbose on or #verbose off: turns on or off the printing of some steps of the computation. The default value is 'off';";
  print_endline "#time on or #time off: turns on or off the measuring of the execution time of a query. The default value is 'off'. (Note that the time measurement of the permutation checking is always on);";
  print_endline "#exit command terminates the program.";
  print_endline "#help displays this message;";
  print_endline "There are the following commands available during state '?>':\n";
  print_endline "#perm: checks if the rules specified in the file permute (all possible combinations of 2 rules).";
  print_endline "#macro: generates the macro rules of each rule of the file loaded.";
  (*print_endline "#coherence: checks is the system specified on the file loaded
  is coherent (If it is a sequent calculus system specified according to the
  guidelines.";*)
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

