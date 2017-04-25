(**************************************)
(*                                    *)
(*       Basic data structure         *)
(*                                    *)
(**************************************)

(** Basic data types. These are the elements that make formulas and terms in
    linear logic with subexponentials. *)

(** Type constructors *)
type types =
| TCONST of basicTypes (** Tonstant (declared) types *)
| TVAR of string       (** Type variables *)
| ARR of types * types (** Function type *)
(**Built-in type constructors for constant types *)
and basicTypes =
| TKIND of string (** Kinds declared by the user *)
| TINT            
| TSTRING
| TPRED           (** Type "o" of formulas (in the meta-logic) *)
| TSUBEX          (** Type of subexponentials *)
| TLIST of basicTypes
;;

(** Polarity of atoms *)
type polarity = 
| POS
| NEG

(** Atoms, formulas, terms, etc.  *)
type terms = 
| PRED of string * terms * polarity (* G: name of the predicate (string) and head (terms) *)
| TOP
| ONE
| BOT
| ZERO
| NOT of terms
(* Arithmetic (comments with one * seem to be ignored.) *)
| EQU of string * int * terms (* G: equality *)
| COMP of compType * terms * terms
| ASGN of terms * terms
| PRINT of terms
| CUT
| TENSOR of terms * terms
| ADDOR of terms * terms
| PARR of terms * terms
(* TODO: remove the subexponential argument from LOLLI *)
| LOLLI of terms * terms * terms
| BANG of terms * terms
| QST of terms * terms
| WITH of terms * terms
| FORALL of string * int * terms
| EXISTS of string * int * terms
| CLS of clType * terms * terms
| VAR of var
| DB of int        (*This seems necessary for head normalization procedure.*)
| INT of int
| CONST of string
| STRING of string
| APP of terms * terms list
| ABS of string * int * terms
| PLUS  of terms * terms
| MINUS of terms * terms
| TIMES of terms * terms 
| DIV of terms * terms
| SUSP of terms * int * int * env
| PTR  of ptr
| NEW of string * terms
| BRACKET of terms
(**/**) (* This is a command to stop documenting. The following definitions and
types will not appear in the documentation generated with ocamldoc. *)
and ptr = in_ptr ref
and in_ptr = V of var | T of terms
and env = envitem list
and envitem = Dum of int | Binding of terms * int
and compType =
| EQ | LESS | GEQ | GRT | LEQ | NEQ
and clType =
| DEF | LOL
and
tag =  (*VN: Tag for variables: either an eigenvariable or a logical variable.
The logical variable points to a term. This is used to instantiate the variable
when performing unification.*)
EIG | CST | LOG
and 
var = {
  str : string;
  id  : int ; (* Only used for hashing *)
  tag : tag ;
  ts  : int ; (* Always zero for constants in Bedwyr *)
  lts : int
}
(**/**)


