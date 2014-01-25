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

(* (Lazy Head) Normalization *)

(* Raise the substitution *)
let rec add_dummies env n m =
  match n with
    | 0 -> env
    | _ -> let n'= n-1 in ((Dum (m+n'))::(add_dummies env n' m))

(** Make an environment appropriate to [n] lambda abstractions applied to
    the arguments in [args]. Return the environment together with any
    remaining lambda abstractions and arguments. (There can not be both
    abstractions and arguments left over). *)
let make_env n args =
  let rec aux n args e = match n, args with
    | 0, _ | _, [] -> e, n, args
    | _, hd::tl -> aux (n-1) tl (Binding(hd, 0)::e)
  (*
    if n = 0 || args = []
    then (e, n, args)
    else aux (n-1) (List.tl args) (Binding(List.hd args, 0)::e)
  *)
  in aux n args []
        
(** Head normalization function.*)
let rec hnorm term =
  match Term.observe term with
    | VAR _
    (*| NB _*)
    | CONST _
    (*| LIST _*)
    | STRING _
    | INT _ | TOP | ONE | BOT | ZERO | CUT
    | DB _ -> term
    | COMP (typ, t1, t2) -> COMP (typ, hnorm t1, hnorm t2)
    | ASGN(t1,t2) -> ASGN(hnorm t1, hnorm t2)
    | PRINT(t1) -> PRINT(hnorm t1)
    | EQU (str, i, t1) -> EQU (str, i,  hnorm t1)
    | CLS(_,_,_) -> failwith "Not expected a clause in hnorm."
    | PRED(str, t1, p) -> PRED(str, hnorm t1, p)
    | TENSOR (t1, t2) -> TENSOR (hnorm t1, hnorm t2)
    | ADDOR (t1, t2) -> ADDOR (hnorm t1, hnorm t2)
    | PARR (t1, t2) -> PARR (hnorm t1, hnorm t2)
    | LOLLI (str, t1, t2) -> LOLLI (hnorm str, hnorm t1, hnorm t2)
    | BANG (str, t1) -> BANG (hnorm str, hnorm t1)
    | HBANG (str, t1) -> HBANG (hnorm str, hnorm t1)
    | QST (str, t1) -> QST (hnorm str, hnorm t1)
    | WITH (t1, t2) -> WITH (hnorm t1, hnorm t2)
    | NOT (t1) -> NOT (hnorm t1)
    | PLUS (t1,t2) -> PLUS (hnorm t1, hnorm t2)
    | MINUS (t1,t2) -> MINUS (hnorm t1, hnorm t2)
    | TIMES (t1,t2) -> TIMES (hnorm t1, hnorm t2)
    | DIV (t1,t2) -> DIV (hnorm t1, hnorm t2)
    | ABS(_,n,t) -> Term.lambda n (hnorm t)
    | FORALL(str,n,t) -> FORALL(str,n,hnorm t)
    | EXISTS(str,n,t) -> EXISTS(str,n,hnorm t)
    | NEW(str,t) -> NEW(str,hnorm t)
    | BRACKET (t) -> BRACKET(hnorm t)
    | APP(t,args) ->
        let t = hnorm t in
          begin match Term.observe t with
            | ABS(_, n,t) ->
                let e, n', args' = make_env n args in
                let ol = List.length e in
                  if n' > 0
                  then hnorm (Term.susp (Term.lambda n' t) ol 0 e)
                  else hnorm (Term.app (Term.susp t ol 0 e) args')
            (*| _ -> Term.app t args*)
            | _ -> Term.app t (List.map hnorm args) (*VN: Replaced this code from the orginal one in Bedwyr. It seems to make more sense.*)
          end
    | SUSP(t,ol,nl,e) ->
        let t = hnorm t in
          begin match Term.observe t with
            (*| NB _ *)
            | CONST _ (*| LIST _*) | STRING _ | INT _ 
            | TOP | ONE | BOT | ZERO | VAR _  | CUT -> t
            | DB i ->
                if i > ol then
                  (* The index points to something outside the suspension *)
                  Term.db (i-ol+nl)
                else
                  (* The index has to be substituted for [e]'s [i]th element *)
                  begin match List.nth e (i-1) with
                    | Dum l -> Term.db (nl - l)
                    | Binding (t,l) -> hnorm (Term.susp t 0 (nl-l) [])
                  end
            | ABS(_,n,t1) ->
                Term.lambda n (hnorm (Term.susp t1 (ol+n) (nl+n)
                                       (add_dummies e n nl)))
            | FORALL(str,n,t1) ->
                FORALL (str, n, hnorm (Term.susp t1 (ol+1) (nl+1)
                                       (add_dummies e 1 nl)))
            | EXISTS(str,n,t1) ->
                EXISTS (str, n, hnorm (Term.susp t1 (ol+1) (nl+1)
                                       (add_dummies e 1 nl)))
            | NEW(str,t1) ->
                NEW (str, hnorm (Term.susp t1 (ol+1) (nl+1)
                                       (add_dummies e 1 nl)))
            | APP(t1,args) ->
                let wrap x = Term.susp x ol nl e in
                  hnorm (Term.app (wrap t1) (List.map wrap args))
            | PRED (str, t1, p) -> PRED(str, hnorm (Term.susp t1 ol nl e), p)
            | COMP (cmp, t1,t2) -> COMP(cmp, hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | ASGN (t1,t2) -> ASGN(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | PRINT (t1) -> PRINT(hnorm (Term.susp t1 ol nl e))
            | EQU (str, i,t1) -> EQU(str, i, hnorm (Term.susp t1 ol nl e))
            | TENSOR (t1,t2) -> TENSOR(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | LOLLI (str, t1,t2) -> LOLLI( hnorm (Term.susp str ol nl e), hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | BANG (str, t1) -> BANG(hnorm (Term.susp str ol nl e), hnorm (Term.susp t1 ol nl e))
            | HBANG (str, t1) -> HBANG(hnorm (Term.susp str ol nl e), hnorm (Term.susp t1 ol nl e))
            | QST (str, t1) -> QST(hnorm (Term.susp str ol nl e), hnorm (Term.susp t1 ol nl e))
            | WITH (t1,t2) -> WITH(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | ADDOR (t1,t2) -> ADDOR(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | PARR (t1,t2) -> PARR(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
	          | BRACKET (f) -> BRACKET(hnorm (Term.susp f ol nl e))
            | NOT (f) -> NOT(hnorm (Term.susp f ol nl e))
            | CLS(typ,t1,t2) -> CLS(typ,hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | PLUS (t1,t2) -> PLUS(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | MINUS (t1,t2) ->  MINUS(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | TIMES (t1,t2) ->  TIMES(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | DIV (t1,t2) ->  DIV(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            (*| SUSP _ -> hnorm (Term.susp (hnorm t) ol nl e)*)
            | PTR _ | SUSP _ -> assert false
          end

    | PTR _-> print_string (Prints.termToString term); assert false

let rec deep_norm t =
  let t = hnorm t in
    match Term.observe t with
      (*| NB _ *)
      | CONST _
      (*| LIST _*)
      | STRING _
      | INT _ | ONE | TOP | BOT | ZERO | CUT
      | VAR _ | DB _ -> t
      | ABS (_,n,t) -> Term.lambda n (deep_norm t)
      | APP (a,b) ->
            begin match Term.observe a with
              | VAR _ 
              (*| NB _ *)
              | DB _ ->
                    Term.app a (List.map deep_norm b)
              | _ -> deep_norm (Term.app (deep_norm a) (List.map deep_norm b))
            end
      | PRED (str,t1, p) -> PRED (str, deep_norm t1, p)
      | EQU (str, i, t1) -> EQU (str, i, deep_norm t1)
      | COMP (cmp, t1,t2) -> COMP (cmp,deep_norm t1, deep_norm t2)
      | ASGN (t1,t2) -> ASGN (deep_norm t1, deep_norm t2)
      | PRINT (t1) -> PRINT (deep_norm t1)
      | TENSOR (t1,t2) -> TENSOR (deep_norm t1, deep_norm t2)
      | ADDOR (t1,t2) -> ADDOR (deep_norm t1, deep_norm t2)
      | PARR (t1,t2) -> PARR (deep_norm t1, deep_norm t2)
      | LOLLI (str, t1,t2) -> LOLLI (deep_norm str, deep_norm t1, deep_norm t2)
      | BANG (str,t1) -> BANG (deep_norm str, deep_norm t1)
      | HBANG (str,t1) -> HBANG (deep_norm str, deep_norm t1)
      | QST (str,t1) -> QST (deep_norm str, deep_norm t1)
      | WITH (t1,t2) -> WITH (deep_norm t1, deep_norm t2)
      | FORALL (str, i, t1) -> FORALL (str, i, deep_norm t1)
      | EXISTS (str, i, t1) -> EXISTS (str, i, deep_norm t1)
      | NEW (str, t1) -> NEW (str, deep_norm t1)
      | BRACKET (f) -> BRACKET(deep_norm f)
      | NOT (f) -> NOT(deep_norm f)
      | CLS (typ, t1, t2) -> CLS (typ, deep_norm t1, deep_norm t2)
      | PLUS (t1,t2) -> PLUS (deep_norm t1, deep_norm t2)
      | MINUS (t1,t2) -> MINUS (deep_norm t1, deep_norm t2)
      | TIMES (t1,t2) -> TIMES (deep_norm t1, deep_norm t2)
      | DIV (t1,t2) -> DIV (deep_norm t1, deep_norm t2)
      | PTR _ 
      | SUSP _ -> assert false




