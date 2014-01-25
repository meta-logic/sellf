(*****************************************)
(*                                       *)
(* Constraint set for reasoning about    *)
(* context variables - interface file    *)
(*                                       *)
(* Giselle Machado Reis                  *)
(* 2013                                  *)
(*                                       *)
(*****************************************)

open Types
open ContextSchema (* After creating the interface, this prefix can be removed,
I think *)

type ctx = string * int
type constraintpred =
  | IN of terms * ctx
  | ELIN of terms * ctx
  | EMP of ctx
  | UNION of ctx * ctx * ctx
  | REQIN_UNB of terms * ctx
  | REQIN_LIN of terms * ctx

type constraintset = {
  mutable lst : constraintpred list;
}

val create : constraintpred list -> constraintset

val union : constraintset -> constraintset -> constraintset

val times : constraintset list -> constraintset list -> constraintset list

val copy : constraintset -> constraintset

val isEmpty : constraintset -> bool

val isIn : terms -> string -> ContextSchema.context -> constraintset

val inEndSequent : terms -> ContextSchema.context -> constraintset list

val requireIn : terms -> (string * int) -> constraintpred

val insert : terms -> string -> ContextSchema.context -> ContextSchema.context -> constraintset

val empty : string -> ContextSchema.context -> constraintset

val split : ContextSchema.context -> ContextSchema.context -> ContextSchema.context -> constraintset

val bang : ContextSchema.context -> string -> constraintset

val initial : ContextSchema.context -> terms -> constraintset list

val predToTexString : constraintpred -> string

val toTexString : constraintset -> string

val predToString : constraintpred -> string

val toString : constraintset -> string
