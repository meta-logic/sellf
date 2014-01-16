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
  | ELIN of Term.terms * ctx
  | EMP of ctx
  | UNION of ctx * ctx * ctx
  | REQIN of Term.terms * ctx
 
type constraintset = {
  mutable lst : constraintpred list;
}

val create : constraintpred list -> constraintset

val union : constraintset -> constraintset -> constraintset 

val times : constraintset list -> constraintset list -> constraintset list

val copy : constraintset -> constraintset

val isEmpty : constraintset -> bool

val isIn : Term.terms -> string -> ContextSchema.context -> constraintset

val inEndSequent : Term.terms -> ContextSchema.context -> constraintset list

val requireIn : Term.terms -> string -> ContextSchema.context -> constraintset

val insert : Term.terms -> string -> ContextSchema.context -> ContextSchema.context -> constraintset

val empty : string -> ContextSchema.context -> constraintset

val split : ContextSchema.context -> ContextSchema.context -> ContextSchema.context -> constraintset

val bang : ContextSchema.context -> string -> constraintset

val initial : ContextSchema.context -> Term.terms -> constraintset list

val predToTexString : constraintpred -> string

val toTexString : constraintset -> string

val predToString : constraintpred -> string

val toString : constraintset -> string


