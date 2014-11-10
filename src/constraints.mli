(*****************************************)
(*                                       *)
(* Constraint set for reasoning about    *)
(* context variables - interface file    *)
(*                                       *)
(* Giselle Machado Reis                  *)
(* 2013                                  *)
(*                                       *)
(*****************************************)

(** DLV constraints. Constraint set for reasoning about context variables. *)

open Types
open ContextSchema (* After creating the interface, this prefix can be removed,
I think *)

(** A generic context is composed by its name and a numeric identifier. *)
type ctx = string * int
(** Constraint types. These are later translated to a dlv file. REQIN_UNB(F, G) is
    translated as ":- not in(F, G)." and REQIN_LIN is translated as ":- not
    in(F, G). :- in(F, G), in(F1, G), F != F1." *)
type constraintpred =
  | IN of terms * ctx
  | EMP of ctx
  | UNION of ctx * ctx * ctx
  | SETMINUS of ctx * terms * ctx
  | REQIN_UNB of terms * ctx
  | REQIN_LIN of terms * ctx

(** A set of constraints is represented internally as a list of constraint
    predicates. Currently we are not concerned about duplicate elements, since
    they are ignored by dlv. *)
type constraintset = {
  mutable lst : constraintpred list;
}

(** Creates a constraint set from a list of constraint predicates. *)
val create : constraintpred list -> constraintset

(** Union of constraint sets. *)
val union : constraintset -> constraintset -> constraintset

(** Cross-product of two sets of constraints. *)
val times : constraintset list -> constraintset list -> constraintset list

(** Creates a copy of this set of constraints. *)
val copy : constraintset -> constraintset

(** Checks if a constraint set is empty *)
val isEmpty : constraintset -> bool

(** Takes a formula F, a subexponential name S and a context C as a parameter
    and creates the constraints indicating that F is in the subexponential S in
    the context C. Generates the correct constraint IN or ELIN depending on the
    type of S. *)
val isIn : terms -> string -> ContextSchema.context -> constraintset

(** Takes a formula F and context C as a parameter and generates the in/elin
    constraints for the end-sequent. This method takes into account the side the
    formula is supposed to be and ignores gamma and infty. It deduces the
    possible initial context for the head of a specification. *)
val inEndSequent : terms -> ContextSchema.context -> constraintset list

(** Takes a formula and F and generic context and generates the constraints that
    require that F is in this generic context. I.e. the program fails if this is
    not the case. *)
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

val isUnion : constraintpred -> bool

val isIn : constraintpred -> bool

val isEmp : constraintpred -> bool

val isMinus : constraintpred -> bool

val isUnbounded : constraintpred -> bool

val isBounded : constraintpred -> bool
