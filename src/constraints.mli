(*****************************************)
(*                                       *)
(*  Constraint set for reasoning about   *)
(*  context variables - interface file   *)
(*                                       *)
(*  Giselle Machado Reis                 *)
(*  2013                                 *)
(*                                       *)
(*****************************************)

type ctx = string * int
type constraintpred = 
  | IN of Term.terms * ctx
  | MCTX of Term.terms * ctx
  | ELIN of Term.terms * ctx
  | EMP of ctx
  | UNION of ctx * ctx * ctx
  | ADDFORM of Term.terms * ctx * ctx
  | REQIN of Term.terms * ctx
  | REMOVED of Term.terms * ctx * ctx
 
type constraintset = {
  mutable lst : constraintpred list;
}

val create : constraintpred list -> constraintset

val union : constraintset -> constraintset -> constraintset 

val times : constraintset list -> constraintset list -> constraintset list

val copy : constraintset -> constraintset

val isEmpty : constraintset -> bool

val isIn : Term.terms -> string -> ContextSchema.context -> constraintset

val requireIn : Term.terms -> string -> ContextSchema.context -> constraintset

val remove : Term.terms -> string -> ContextSchema.context -> ContextSchema.context -> constraintset

val insert : Term.terms -> string -> ContextSchema.context -> ContextSchema.context -> constraintset

val empty : string -> ContextSchema.context -> constraintset

val split : ContextSchema.context -> ContextSchema.context -> ContextSchema.context -> constraintset

val bang : ContextSchema.context -> string -> constraintset

val initial : ContextSchema.context -> Term.terms -> constraintset list

val ctxToTex : string * int -> string

val ctxToStr : string * int -> string

val predToTexString : constraintpred -> string

val toTexString : constraintset -> string

val predToString : constraintpred -> string

val toString : constraintset -> string


