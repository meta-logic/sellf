(****************************************************************************)
(* An implementation of Higher-Order Pattern Unification                    *)
(* Copyright (C) 2006-2009 Nadathur, Linnell, Baelde, Ziegler               *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

open Types

(** Higher Order Pattern Unification *)

type error =
  | OccursCheck
  | TypesMismatch
  | ConstClash of (terms * terms)

exception Error of error
exception NotLLambda of terms

let not_ll x = raise (NotLLambda x)
let raise e = raise (Error e)

module type Param =
sig
  val instantiatable : tag
  val constant_like  : tag
end

module Make (P:Param) =
struct

open P
open Term

(*let (isLeft, isRight) = (P.instantiatable = EIG, P.instantiatable = LOG)*)

let constant tag =
  tag = CST || tag = constant_like
let variable tag =
  tag = instantiatable
let fresh = fresh instantiatable

(* Transforming a term to represent substitutions under abstractions *)
let rec lift t n = match Term.observe t with
  | VAR _ -> t
  | DB i -> db (i+n)
  | _ -> susp t 0 n []

(* Transforming a list of arguments to represent eta fluffing *)
let rec lift_args l n = match l,n with
  | [],0 -> []
  | [],n -> (db n)::lift_args [] (n-1)
  | (a::rargs),n -> (lift a n)::lift_args rargs n

(* Check wether a Var appears in a list of terms *)
let rec unique_var v = function
  | [] -> true
  | t::rargs  ->
      begin match Term.observe t with
        | VAR v' when v=v' -> false
        | _ -> unique_var v rargs
      end

(* Check if a bound variable appears in a list of term *)
let rec unique_bv n l = match l with
  | [] -> true
  | t::rargs ->
      begin match Term.observe t with
        | DB j when n = j -> false
        | _ -> unique_bv n rargs
      end

(*let rec unique_nb n l = match l with
  | [] -> true
  | t::tl ->
      begin match Term.observe t with
        | NB j when j=n -> false
        | _ -> unique_nb n tl
      end*)

(** [check_flex_args l fts] checks that a list of terms meets the LLambda
  * requirements for the arguments of a flex term whose timestamp is [fts].
  * @raise NotLLambda if the list doesn't satisfy the requirements. *)
let rec check_flex_args l fts flts =
  match l with
    | [] -> ()
    | t::q ->
        begin match Term.observe t with
          | VAR v when constant v.tag && v.ts>fts && unique_var v q ->
              check_flex_args q fts flts
          | DB i when unique_bv i q -> check_flex_args q fts flts
         (* | NB i when i>flts && unique_nb i q -> check_flex_args q fts flts*)
          | _ -> not_ll t
        end

(** Simple occurs-check and level check to allow unification in very
  * simple non-llambda cases (when check_flex_args fails).
  * Assumes head-normalization of [t].
  *
  * XXX Note that the level checks are useless on the left (this is in fact
  * true everywhere in this module) and that making them tighter on the right
  * can be dangerous. In a nutshell: this is very simple but suffices. *)

(*VN: I did not change the function below, as I am assuming that we are always in the 
LLambda fragment.*)
let can_bind v t =
  let rec aux n t =
    match Term.observe t with
      | VAR v' ->
          ((*isLeft ||*) (v' <> v && v'.ts <= v.ts)) && v'.lts <= v.lts
      | DB i -> i <= n
      (*| NB j -> j <= v.lts*)
      | ABS (_, n', t) -> aux (n+n') t
      | APP (h, ts) ->
          aux n h && List.for_all (aux n) (List.map Norm.hnorm ts)
      | SUSP _ | PTR _ | DIV _ | TIMES _ | MINUS _ | PLUS _ (*| LIST _*) | STRING _ | CONST _ | INT _-> assert false
      | _ -> failwith "Not expected term in function 'can_bind', unify.ml"
  in
    aux 0 t

(** [bvindex bv l n] return a nonzero index iff the db index [bv]
  * appears in [l]; the index is the position from the right, representing
  * the DeBruijn index of the abstraction capturing the argument.
  * Arguments in the list are expected to be head-normalized. *)
let rec bvindex i l n = match l with
  | [] -> 0
  | t::q ->
     begin match Term.observe t with
       | DB j when i=j -> n
       | _ -> bvindex i q (n-1)
     end

(*let rec nbindex i l n = match l with
  | [] -> 0
  | t::q ->
     begin match Term.observe t with
       | Term.NB j when i=j -> n
       | _ -> nbindex i q (n-1)
     end*)

(** [cindex c l n] return a nonzero index iff the constant [c]
  * appears in [l]; the index is the position from the right, representing
  * the DeBruijn index of the abstraction capturing the argument.
  * Arguments in the list are expected to be head-normalized. *)
let rec cindex c l n = match l with
  | [] -> 0
  | t::q ->
      begin match Term.observe t with
        | VAR c' when c = c' -> n
        | _ -> cindex c q (n-1)
      end

(** Given a flexible term [v1 a11 ... a1n] and another term of the form 
  * [... (v2 a21 ... a2m) ...] where [v1] and [v2] are distinct variables,
  * [ts1] and [ts2] being the timestamps associated with [v1] and [v2],
  * and [lev] being the number of abstractions under which [v2] appears
  * embedded in the second term,
  * [raise_and_invert ts1 ts2 [a11 .. a1n] [a21 .. a2m] lev]
  * return a triple consisting of:
  *
  * {ul
  * {li a truth value indicating whether a pruning or raising
  * substitution is needed for [v2],}
  * {li a list of terms [b1 ... bk] such that the term 
  * [Lam ... Lam (... (v2' b1 ... bk) ...] 
  * represents a unifying substitution for [v1] -- these terms 
  * consist of constants from [a11 ... a1n] over which [v2] is
  * possibly raised and inversions of a pruned [a21 ... a2m], and}
  * {li the arguments [c1 ... ck] of a possible "raising" and pruning
  * substitution for [v2] matching the arguments [b1 ... bk] for
  * [v2'] in the second component.}}
  *
  * The composition of the arguments lists can be understood
  * qualitatively as follows:
  *
  * If [ts1 < ts2] then {ul{li the initial part of
  * [b1 ... bk] is the indices of constants from [a11 ... a1n] that do
  * not appear in [a21 ... a2m] and that have a timestamp less than or 
  * equal to [ts2] (this corresponds to raising [v2]) and} {li the rest of 
  * [b1 ... bk] are the indices (relative to the list a11 ... a1n) of 
  * the constants in [a21 ... a2m] that appear in [a11 ... a1n] (these are 
  * the arguments that must not be pruned).}} Correspondingly, the first
  * part of the list [c1 ... ck] are the constants from [a11 ... a1n] over
  * which [v2] is "raised" and the second part are the indices relative
  * to [a21 ... a2m] of the constants that are not pruned.
  *
  * If [ts1 >= ts2]
  * then each of [b1 ... bk] is either {ul{li a constant in [a21 ... a2m] that
  * does not appear in [a11 ... a1n] and which has a timestamp less than
  * [ts1] (this corresponds to first raising [v1] and then reducing the
  * substitution generated for [v1])} {li or it is the index, relative to 
  * [a11 ... a1n], of the terms in [a21 ... a2m] that are in 
  * [a11 ... a1n].}}
  * The list [c1 ... ck] in this case are simply the indices
  * relative to [a21 ... a2m] of the terms in [a21 ... a2m] that are
  * preserved (i.e. not pruned) in [b1 ... bk].
  *
  * This definition assumes that the [aij] are in
  * head-normal form and that [a1] satisfies the LLambda 
  * requirements. If [a2] does not satisfy these requirements, an
  * exception will be raised. *)
let raise_and_invert v1 v2 a1 a2 lev =
  let stamps = function {ts=ts;lts=lts} -> ts,lts in
  let ts1,lts1 = stamps v1 in
  let ts2,lts2 = stamps v2 in
  let l1 = List.length a1 in

  (* [raise_var args n] generates the collection of
   * constants in [args] that have a time stamp less than [ts2],
   * assuming [n] is the index for the abstraction corresponding
   * to the first term in [args]. In other words, constants which cannot
   * appear in [v2]'s body.
   * This serves to raise [v2] in the case where [ts1 < ts2]. The boolean
   * component of the returned triple tells if there is
   * any raising to be done. The terms in [args] are assumed to be
   * constants or de Bruijn indices, as head normalized
   * arguments satisfying the LLambda restriction. *)
  let rec raise_var l n = match l with
    | [] -> false,[],[]
    | t::tl ->
        begin match Term.observe t with
          | DB _ -> raise_var tl (n-1)
          (*| Term.NB j ->
              let raised,inds,consts = raise_var tl (n-1) in
                if j <= lts2 then
                  (true,(DB (n+lev))::inds,t::consts)
                else
                  raised,inds,consts*)
          | VAR {ts=cts;tag=tag} when constant tag ->
              let raised,inds,consts = raise_var tl (n-1) in
                if cts <= ts2 then
                  (true,(DB (n+lev))::inds,t::consts)
                else
                  (raised,inds,consts)
          | _ -> assert false
        end
  in

  (** [prune args n] "prunes" those items in [args] that are not
    * bound by an embedded abstraction and that do not appear in
    * [a1]. At the same time inverts the items that are not pruned
    * and that are not bound by an embedded abstraction; [n] is assumed to be
    * the length of [args] here and hence yields the index of the
    * leftmost argument position. This pruning computation is
    * relevant to the case when [ts1 < ts2]. The terms in [args]
    * are assumed to be constants or de Bruijn or nabla indices. *)
  let rec prune l n = match l,n with
    | [],0 -> false,[],[]
    | t::q,n ->
        begin match Term.observe t with
          | DB i -> 
              let pruned,inds1,inds2 = prune q (n-1) in
                if i > lev then
                  let j = bvindex (i-lev) a1 l1 in
                    if j = 0 then
                      (true,inds1,inds2) 
                    else
                      (pruned,
                       (DB (j+lev))::inds1,
                       (DB n)::inds2)
                else
                  (pruned,t::inds1,(DB n)::inds2)
          | VAR v when constant v.tag ->
              let pruned,inds1,inds2 = prune q (n-1) in
              let j = cindex v a1 l1 in
                if j = 0 then
                  (true,inds1,inds2)
                else
                  (pruned,
                   (DB (j+lev))::inds1,
                   (DB n)::inds2)
          (*| NB i ->
              let pruned,inds1,inds2 = prune q (n-1) in
              let j = nbindex i a1 l1 in
                if j = 0 then
                  (true,inds1,inds2)
                else
                  (pruned,
                   (DB (j+lev))::inds1,
                   (DB n)::inds2)*)
          | _ -> assert false
        end
    | _ -> assert false
  in

  (** Relevant to the case when [ts1 > ts2]. In this case,
    * [prune_and_raise args n] prunes those constants and de
    * Bruijn indices not bound by an embedded abstraction that do
    * not appear in [a1] and, in the case of constants, that have
    * a timestamp greater than [ts1]. These constants are preserved
    * via a raising of [v1].
    * As in prune, [n] is assumed to be the length of the list
    * args. The terms in [args] are assumed to be constants, nabla or
    * de Bruijn indices. *)
  let rec prune_and_raise l n = match l,n with
    | [],0 -> false,[],[]
    | a::q,n ->
        begin match Term.observe a with
          | DB i -> 
              let pruned,inds1,inds2 = prune_and_raise q (n-1) in
                if i > lev then
                  let j = bvindex (i-lev) a1 l1 in
                    if j = 0 then
                      (true,inds1,inds2)
                    else
                      (pruned,
                       (DB (j+lev))::inds1,
                       (DB n)::inds2)
                else
                  (pruned,a::inds1,(DB n)::inds2)
          (*| Term.NB i ->
              let pruned,inds1,inds2 = prune_and_raise q (n-1) in
                if i <= lts1 then
                  pruned,a::inds1,(DB n)::inds2
                else
                  let j = nbindex i a1 l1 in
                    if j = 0 then
                      (true,inds1,inds2)
                    else
                      (pruned,
                       (DB (j+lev))::inds1,
                       (DB n)::inds2)*)
          | VAR v when constant v.tag -> 
              let pruned,inds1,inds2 = prune_and_raise q (n-1) in
                if v.ts <= ts1 then
                  (pruned,a::inds1,(DB n)::inds2)
                else
                  let i = cindex v a1 l1 in
                    if i=0 then
                      (true,inds1,inds2)
                    else
                      (pruned,
                       (DB (i+lev))::inds1,
                       (DB n)::inds2)
          | _ -> assert false
        end
    | _ -> assert false
  in
    if ts1<ts2 || lts1<lts2 then
      let raised,args_r1,args_r2 = raise_var a1 l1 in
      let pruned,args_p1,args_p2 = prune a2 (List.length a2) in
        (raised||pruned,args_r1@args_p1,args_r2@args_p2)
    else
      prune_and_raise a2 (List.length a2)

(* Generating the arguments of a pruning substitution for the case
 * when trying to unify two flexible terms of the form (v t_1 ... t_n)
 * and lam ... lam (v s_1 ... s_m) where there are j abstractions at the 
 * head of the second term. The first two arguments to prune_same_var
 * are the two lists of arguments, the third argument is j (i.e. the
 * number of abstractions at the head) and the last argument is n+j. It
 * is assumed that type consistency has been checked beforehand,
 * i.e. n+j is indeed equal to m and also that the two argument lists
 * are known to be of the form required for LLambda unification. The
 * computation essentially does the eta fluffing of the first term on
 * the fly (i.e. each t_i has to be lifted over j abstractions and and
 * j new arguments bound by these abstractions are added to the first
 * term). *)
let rec prune_same_var l1 l2 j bl = match l1,l2 with
  | [],[] -> []
  | [],t::q ->
      begin match Term.observe t with
        | DB i when i=j ->
            (DB bl)::(prune_same_var [] q (j-1) (bl-1))
        | _ -> prune_same_var [] q (j-1) (bl-1)
      end
  | t1::a1,t2::a2 ->
      begin match Term.observe t1,Term.observe t2 with
        | VAR {tag=tag1},VAR {tag=tag2}
          when constant tag1 && Term.eq t1 t2 ->
            (DB bl)::(prune_same_var a1 a2 j (bl-1))
        (*| Term.NB i, Term.NB j when i=j ->
            (DB bl)::(prune_same_var a1 a2 j (bl-1))*)
        | DB i1,DB i2 when i1+j = i2 ->
            (DB bl)::(prune_same_var a1 a2 j (bl-1))
        | _ -> prune_same_var a1 a2 j (bl-1)
      end
  | _ -> assert false

(** [makesubst h1 t2 a1] unifies [App (h1,a1) = t2].
  * Given a term of the form [App (h1,a1)] where [h1] is a variable and
  * another term [t2], generate an LLambda substitution for [h1] if this is 
  * possible, making whatever pruning and raising substitution that are
  * necessary to variables appearing within [t2].
  *
  * [t2] is assumed to be in head normal form, [h1] and [a1] are assumed to be
  * dereferenced.
  * 
  * Exceptions can be raised from this code if there is
  *  - a non LLambda situation or
  *  - a failure in unification or
  *  - a type mismatch (if an a priori type checking has not been done).
  *
  * The unification computation is split into two parts, one that
  * examines the top level structure of [t2] and the other that descends
  * into its nested subparts. This organization is useful primarily
  * because [h1], the variable head of the first term can appear at the
  * toplevel in t2 without sacrificing unifiability but not in a nested
  * part. *)
let makesubst h1 t2 a1 =
  let n = List.length a1 in
  (* Check that h1 is a variable, get its timestamps *)
  let v1,ts1,lts1 = match Term.observe h1 with
    | VAR v -> assert (v.tag=instantiatable) ; v,v.ts,v.lts
    | _ -> assert false
  in
  let a1 = List.map Norm.hnorm a1 in

  (** Generating a substitution term and performing raising and
    * pruning substitutions corresponding to a non top-level
    * (sub)term. In this case the variable being bound cannot appear
    * embedded inside the term. This code assumes that its term
    * argument is head normalized. Exceptions can be
    * raised if unification fails or if LLambda conditions are found
    * to be violated. *)
  let rec nested_subst c lev =
    match Term.observe c with
      | VAR v when constant v.tag ->
          (* Can [h1] depend on [c] ?
           * If so, the substitution is [c] itself, and the llambda restriction
           * ensures that this is the only solution.
           * If not, [c] must belong to the argument list. *)
          if v.ts <= ts1 && v.lts <= lts1 then c else
            let j = cindex v a1 n in
              if j = 0 then raise OccursCheck ;
              DB (j+lev)
      (*| Term.NB i ->
          if i <= lts1 then c else
            let j = nbindex i a1 n in
              if j = 0 then raise OccursCheck ;
              DB (j+lev)*)
      | CONST _ ->  c
      | STRING _ ->  c
      | INT _ | ONE | TOP | CUT ->  c
      | DB i ->
          if i <= lev then c else
            let j = bvindex (i-lev) a1 n in
              if j = 0 then raise OccursCheck ;
              DB (j+lev)
      | VAR v2 when variable v2.tag ->
          if Term.eq c h1 then raise OccursCheck ;
          let (changed,a1',a2') = raise_and_invert v1 v2 a1 [] lev in
            if changed || not (lts1 >= v2.lts && ((*isLeft ||*) ts1 >= v2.ts)) then
              let h'= fresh ~lts:(min lts1 v2.lts) ~ts:(min ts1 v2.ts) in
                Term.bind c (Term.app h' a2') ;
                Term.app h' a1'
            else
              Term.app c a1'
      | ABS (_,n,t) ->
          Term.lambda n (nested_subst t (lev+n))
      | APP (h2,a2) ->
          begin match Term.observe h2 with
            | VAR {tag=tag} when constant tag ->
                Term.app
                  (nested_subst h2 lev)
                  (List.map (fun x -> nested_subst (Norm.hnorm x) lev) a2)
            | DB _ (* | Term.NB _*) | CONST _ ->
                Term.app
                  (nested_subst h2 lev)
                  (List.map (fun x -> nested_subst (Norm.hnorm x) lev) a2)
            | VAR v2 when variable v2.tag ->
                if Term.eq h2 h1 then raise OccursCheck ;
                let a2 = List.map Norm.hnorm a2 in
                let ts2,lts2 = v2.ts,v2.lts in
                check_flex_args a2 ts2 lts2 ;
                let changed,a1',a2' = raise_and_invert v1 v2 a1 a2 lev in
                  if changed then
                    let h' = fresh ~lts:(min lts1 v2.lts) ~ts:(min ts1 ts2) in
                      Term.bind h2
                        (Term.lambda (List.length a2) (Term.app h' a2')) ;
                      Term.app h' a1'
                  else
                    if not (lts1 >= lts2 && ((*isLeft || *)ts1 >= ts2)) then
                      let h' = fresh ~lts:(min lts1 v2.lts) ~ts:ts1 in
                        Term.bind h2 h' ;
                        Term.app h' a1'
                    else 
                      Term.app h2 a1'
            | VAR _ -> failwith "logic variable on the left"
            | PTR _ -> assert false  (*VN: The following cannot appear in the head of applications of terms that are normalized.*)
            | SUSP _ -> assert false
            | APP _ -> assert false
            | ABS _ -> assert false (*VN: Term is normalized, so no ABS can appear in the head of applications.*)
            | STRING _ | INT _ -> assert false
            | PLUS _ ->  assert false
            | MINUS _ ->  assert false
            | TIMES _ ->  assert false
            | DIV _ ->  assert false
            | _ -> failwith "Not expected term in function 'nested_subst', unify.ml"
            (*| LIST _ ->  assert false*)
          end
      | VAR _ -> failwith "logic variable on the left"
      | PRED(str, t1, p) -> PRED(str, nested_subst (Norm.hnorm t1) lev, p)
      | COMP(cmp, t1, t2) -> COMP(cmp, nested_subst (Norm.hnorm t1) lev, nested_subst (Norm.hnorm t2) lev)
      | ASGN(t1, t2) -> ASGN(nested_subst (Norm.hnorm t1) lev, nested_subst (Norm.hnorm t2) lev)
      | PRINT(t1) -> PRINT(nested_subst (Norm.hnorm t1) lev)
      | TENSOR(t1, t2) -> TENSOR(nested_subst (Norm.hnorm t1) lev, nested_subst (Norm.hnorm t2) lev)
      | WITH(t1, t2) -> WITH(nested_subst (Norm.hnorm t1) lev, nested_subst (Norm.hnorm t2) lev)
      | LOLLI(str, t1, t2) -> LOLLI(nested_subst (Norm.hnorm str) lev, nested_subst (Norm.hnorm t1) lev, nested_subst (Norm.hnorm t2) lev)
      | BANG(str, t1) -> BANG(nested_subst (Norm.hnorm str) lev , nested_subst (Norm.hnorm t1) lev)
      | FORALL(str, i, t) -> FORALL(str, i, nested_subst t (lev+n))
      | NEW(str, t) -> NEW(str, nested_subst t (lev+n))
      | BRACKET(t) -> BRACKET(nested_subst (Norm.hnorm t) (lev+n))
      | CLS(cmp, t1, t2) -> CLS(cmp, nested_subst (Norm.hnorm t1) lev, nested_subst (Norm.hnorm t2) lev)
      | PLUS (t1,t2) -> Term.plus (List.map (fun x -> nested_subst (Norm.hnorm x) lev) [t1;t2])
      | MINUS (t1,t2) -> Term.minus (List.map (fun x -> nested_subst (Norm.hnorm x) lev) [t1;t2])
      | TIMES (t1,t2) -> Term.times (List.map (fun x -> nested_subst (Norm.hnorm x) lev) [t1;t2])
      | DIV (t1,t2) -> Term.div (List.map (fun x -> nested_subst (Norm.hnorm x) lev) [t1;t2])
      (*| LIST _ -> failwith "lists are not implemented."*)
      | _ -> assert false
  in

  (** Processing toplevel structure in generating a substitution.
    * First descend under abstractions. Then if the term is a
    * variable, generate the simple substitution. Alternatively, if
    * it is an application with the variable being bound as its head,
    * then generate the pruning substitution. In all other cases,
    * pass the task on to nested_subst. An optimization is possible
    * in the case that the term being examined has no outer
    * abstractions (i.e. lev = 0) and its head is a variable with a
    * time stamp greater than that of the variable being bound. In
    * this case it may be better to invoke raise_and_invert
    * directly with the order of the "terms" reversed.
    *
    * The incoming term is assumed to be head normalized. *)

  let rec toplevel_subst t2 lev =
    match Term.observe t2 with
      | ABS (_,n,t2) -> toplevel_subst t2 (lev+n)
      | VAR v2 when variable v2.tag ->
          if h1=t2 then
            if n=0 && lev=0 then h1 else raise TypesMismatch
          else begin
            if not (lts1 >= v2.lts && ((*isLeft ||*) (ts1 >= v2.ts))) then
              Term.bind t2
                (fresh ~lts:(min lts1 v2.lts) ~ts:(min ts1 v2.ts)) ;
            Term.lambda (lev+n) t2
          end
      (* TODO the following seems harmless, and is sometimes useful..
      | VAR v2 when not (constant v2.tag) && a1=[] ->
          Term.lambda lev t2 (* [n] is 0 *)
      *)
      | APP (h2,a2) ->
          begin match Term.observe h2 with
            | VAR {ts=ts2;lts=lts2} when Term.eq h1 h2 ->
                (* FIXME: h1 is a pointer and h2 a variable. They are not equal.
                What should be done?? *)
                (* [h1] being instantiatable, no need to check it for [h2] *)
                let a2 = List.map Norm.hnorm a2 in
                check_flex_args a2 ts2 lts2 ;
                let bindlen = n+lev in
                  if bindlen = List.length a2 then
                    let h1' = fresh ~lts:lts1 ~ts:ts1 in
                    let args = prune_same_var a1 a2 lev bindlen in
                      Term.lambda bindlen (Term.app h1' args)
                  else
                    raise TypesMismatch
            | APP _ | ABS _
            | VAR _ | DB _ (*| Term.NB _*) | CONST _ ->
                Term.lambda (n+lev) (nested_subst t2 lev)
            | SUSP _ | PTR _ -> assert false
            | STRING _ | INT _ -> assert false (*VN: The following cannot appear in the head of applications.*)
            | PLUS _ ->  assert false
            | MINUS _ ->  assert false
            | TIMES _ ->  assert false
            | DIV _ ->  assert false
            | ONE | TOP | BOT | ZERO | EQU _ | COMP _ | ASGN _ | PRINT _ | CUT 
            | TENSOR _ | LOLLI _ | BANG _ |  QST _ | WITH _ | ADDOR _ | PARR _ 
            | FORALL _ | EXISTS _ | NEW _ | PRED _  | CLS _ | BRACKET _
            | NOT _ -> assert false
            (*| LIST _ ->  assert false*)
          end
      | PTR _ -> assert false
      | _ -> Term.lambda (n+lev) (nested_subst t2 lev)
  in

    try
      check_flex_args a1 ts1 lts1 ;
      toplevel_subst t2 0
    with
      | NotLLambda e ->
          (* Not a pattern: try a very strict occurs-check to allow
           * simple cases of the form v1=t2. *)
          if a1 = [] && (can_bind v1 t2) then
            t2
          else
            not_ll e

(** Unifying the arguments of two rigid terms with the same head, these
  * arguments being given as lists. Exceptions are raised if
  * unification fails or if there are unequal numbers of arguments; the
  * latter will not arise if type checking has been done. *)
let rec unify_list l1 l2 =
  try
    List.iter2 (fun a1 a2 -> unify (Norm.hnorm a1) (Norm.hnorm a2)) l1 l2
  with
    | Invalid_argument _ -> raise TypesMismatch

(* [unify_const_term cst t2] unify [cst=t2], assuming that [cst] is a constant.
 * Fail if [t2] is a variable or an application.
 * If it is a lambda, binders need to be equalized and so this becomes
 * an application-term unification problem. *)
and unify_const_term cst t2 = if Term.eq cst t2 then () else
  match Term.observe t2 with
    | ABS (_,n,t2) ->
        let a1 = lift_args [] n in
          unify_app_term cst a1 (Term.app cst a1) t2
    | VAR {tag=t} when not (variable t || constant t) ->
        failwith "logic variable on the left"
    | _ -> raise (ConstClash (cst,t2))

(* Unifying the bound variable [t1] with [t2].
 * Fail if [t2] is a variable, an application or a constant.
 * If it is a lambda, binders need to be
 * equalized and this becomes an application-term unification problem. *)
and unify_bv_term n1 t1 t2 = match Term.observe t2 with
  | DB n2 ->
      if n1<>n2 then raise (ConstClash (t1,t2))
  (*| Term.NB n2 ->
      raise (ConstClash (t1,t2))*)
  | ABS (_,n,t2)  ->
      let t1' = lift t1 n in
      let a1 = lift_args [] n in
        unify_app_term t1' a1 (Term.app t1' a1) t2
  | VAR {tag=t} when not (variable t || constant t) ->
      failwith "logic variable on the left"
  | _ -> assert false

(* Unifying the nabla variable [t1] with [t2]. *)
and unify_nv_term n1 t1 t2 = match Term.observe t2 with
 (* | Term.NB n2 ->
      if n1<>n2 then raise (ConstClash (t1,t2))*)
  | DB n2 ->
      raise (ConstClash (t1,t2))
  | ABS (_,n,t2) ->
      let a1 = lift_args [] n in
        unify_app_term t1 a1 (Term.app t1 a1) t2
  | VAR {tag=t} when not (variable t || constant t) ->
      failwith "logic variable on the left"
  | _ -> assert false

(* [unify_app_term h1 a1 t1 t2] unify [App h1 a1 = t2].
 * [t1] should be the term decomposed as [App h1 a1].
 * [t2] should be dereferenced and head-normalized, different from a var. *)
and unify_app_term h1 a1 t1 t2 = match Term.observe h1,Term.observe t2 with
  | VAR {tag=tag}, _ when variable tag ->
      Term.bind h1 (makesubst h1 t2 a1)
  | VAR {tag=tag}, APP (h2,a2) when constant tag ->
      begin match Term.observe h2 with
        | VAR {tag=tag} when constant tag ->
            if Term.eq h1 h2 then
              unify_list a1 a2
            else
              raise (ConstClash (h1,h2))
        | DB _ (*| NB _*) ->
            raise (ConstClash (h1,h2))
        | VAR {tag=tag} when variable tag ->
            Term.bind h2 (makesubst h2 t1 a2)
        | VAR {tag=t} ->
            failwith "logic variable on the left"
        | _ -> assert false
      end
  (*| Term.NB n1, APP (h2,a2) ->
      begin match Term.observe h2 with
        | DB n2 -> raise (ConstClash (h1,h2))
        | Term.NB n2 ->
            if n1=n2 then unify_list a1 a2 else raise (ConstClash (h1,h2))
        | VAR v ->
            if constant v.tag then
              raise (ConstClash (h1,h2))
            else if variable v.tag then
              Term.bind h2 (makesubst h2 t1 a2)
            else
              failwith "logic variable on the left"
        | _ -> assert false
      end*)
  | DB n1, APP (h2,a2) ->
      begin match Term.observe h2 with
       (* | Term.NB n2 -> raise (ConstClash (h1,h2))*)
        | DB n2 ->
            if n1=n2 then unify_list a1 a2 else raise (ConstClash (h1,h2))
        | VAR v ->
            if constant v.tag then
              raise (ConstClash (h1,h2))
            else if variable v.tag then
              Term.bind h2 (makesubst h2 t1 a2)
            else
              failwith "logic variable on the left"
        | _ -> assert false
      end
  | _, ABS (_,n,t2) ->
      let h1' = lift h1 n in
      let a1' = lift_args a1 n in
      let t1' = Term.app h1' a1' in
        unify_app_term h1' a1' t1' t2
  | PTR  _, _ | _, PTR  _
  | SUSP _, _ | _, SUSP _ -> assert false
  | _, VAR {tag=t}
  | VAR {tag=t}, _ when not (variable t || constant t) ->
      failwith "logic variable on the left"
  | CONST(head1), APP(h, a2) when h = h1 -> unify_list a1 a2
  | _ -> raise (ConstClash (h1,t2))

(** The main unification procedure.
  * Either succeeds and realizes the unification substitutions as side effects
  * or raises an exception to indicate nonunifiability or to signal
  * a case outside of the LLambda subset. When an exception is raised,
  * it is necessary to catch this and at least undo bindings for
  * variables made in the attempt to unify. This has not been included
  * in the code at present.
  * 
  * This procedure assumes that the two terms it gets are in
  * head normal form and that there are no iterated
  * lambdas or applications at the top level. Any necessary adjustment
  * of binders through the eta rule is done on the fly. *)
and unify t1 t2 = match Term.observe t1,Term.observe t2 with
  | VAR {tag=t},_ when variable t -> Term.bind t1 (makesubst t1 t2 [] )
  | _,VAR {tag=t} when variable t -> Term.bind t2 (makesubst t2 t1 [])
  | APP (h1,a1),_                 -> unify_app_term h1 a1 t1 t2
  | _,APP (h2,a2)                 -> unify_app_term h2 a2 t2 t1
  | VAR {tag=t},_ when constant t -> unify_const_term t1 t2
  | _,VAR {tag=t} when constant t -> unify_const_term t2 t1
  | DB n,_                        -> unify_bv_term n t1 t2
  | _,DB n                        -> unify_bv_term n t2 t1
  | PRED(str1, t1, p1), PRED(str2, t2, p2) -> 
      if str1 = str2 then       
        unify t1 t2 
      else failwith "ERROR: Unifying two predicates with different strings."
  | EQU (str1, i1, t1), EQU (str2, i2, t2) -> 
      if str1 = str2 && i1 = i2 then 
        unify t1 t2 
      else failwith "ERROR: Unifying two EQUs with different strings or different integers."
  | TOP, TOP | ONE, ONE | CUT, CUT -> ()
  | COMP (cmp1, a1, b1), COMP (cmp2, a2, b2) -> 
      if cmp1 = cmp2 then 
        unify_list [a1;b1] [a2;b2]
      else failwith "ERROR: Unifying two CMPs of different types."
  | ASGN (a1, b1), ASGN (a2, b2) -> 
        unify_list [a1;b1] [a2;b2]
  | PRINT (a1), PRINT (a2) -> 
        unify a1 a2 
  | TENSOR (a1,b1), TENSOR (a2,b2)  -> unify_list [a1;b1] [a2;b2]
  | BRACKET (a1), BRACKET (a2)  -> unify a1 a2
  | LOLLI (str1 ,a1, b1), LOLLI (str2, a2, b2)  -> 
        unify_list [str1; a1;b1] [str2; a2;b2]
  | BANG (str1 ,a), BANG (str2, b)  -> 
        unify_list [str1; a] [str2; b]
  | WITH (a1,b1), WITH (a2,b2)  -> unify_list [a1;b1] [a2;b2]
  | FORALL (str1, i1, t1), FORALL (str2, i2, t2) -> 
        unify (ABS(str1, 1, t1))  (ABS(str1, 1, t1)) (*VN: FORALL are like abstractions.*)
  | NEW (str1, t1), NEW (str2, t2) -> 
        unify (ABS(str1, 1, t1))  (ABS(str1, 1, t1)) (*VN: NEW are like abstractions.*)
  | CLS(cmp1, a1, b1), CLS(cmp2, a2, b2) -> 
    if cmp1 = cmp2 then 
      unify_list [a1;b1] [a2;b2]
    else failwith "ERROR: Unifying two CLSs of different types."
  | PLUS (a1,b1), PLUS (a2,b2)  -> unify_list [a1;b1] [a2;b2]
  | MINUS (a1,b1), MINUS (a2,b2)  -> unify_list [a1;b1] [a2;b2]
  | TIMES (a1,b1), TIMES (a2,b2)  -> unify_list [a1;b1] [a2;b2]
  | DIV (a1,b1), DIV (a2,b2)  -> unify_list [a1;b1] [a2;b2]
  | CONST(c1), CONST(c2)  -> if c1 = c2 then () else failwith "ERROR: Unifying different constants."
  | STRING(c1), STRING(c2)  -> if c1 = c2 then () else failwith "ERROR: Unifying different constants."
  | INT(c1), INT(c2)  -> if c1 = c2 then () else failwith "ERROR: Unifying different constants."
  (*| Term.NB n,_                        -> unify_nv_term n t1 t2*)
  (*| _,Term.NB n                        -> unify_nv_term n t2 t1*)
  | ABS (_,n1,t1),ABS(_,n2,t2)   ->
      if n1>n2 then
        unify (Term.lambda (n1-n2) t1) t2
      else
        unify t1 (Term.lambda (n2-n1) t2)
  | _ -> failwith "logic variable on the left"

let pattern_unify t1 t2 = unify (Norm.hnorm t1) (Norm.hnorm t2)

end
