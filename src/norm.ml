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

(* (Lazy Head) Normalization *)

(* Raise the substitution *)
let rec add_dummies env n m =
  match n with
    | 0 -> env
    | _ -> let n'= n-1 in ((Term.Dum (m+n'))::(add_dummies env n' m))

(** Make an environment appropriate to [n] lambda abstractions applied to
    the arguments in [args]. Return the environment together with any
    remaining lambda abstractions and arguments. (There can not be both
    abstractions and arguments left over). *)
let make_env n args =
  let rec aux n args e =
    if n = 0 || args = []
    then (e, n, args)
    else aux (n-1) (List.tl args) (Term.Binding(List.hd args, 0)::e)
  in aux n args []
        
(** Head normalization function.*)
let rec hnorm term =
  match Term.observe term with
    | Term.VAR _
    (*| Term.NB _*)
    | Term.CONS _
    (*| Term.LIST _*)
    | Term.STRING _
    | Term.INT _ | Term.TOP | Term.ONE | Term.CUT
    | Term.DB _ -> term
    | Term.COMP (typ, t1, t2) -> Term.COMP (typ, hnorm t1, hnorm t2)
    | Term.ASGN(t1,t2) -> Term.ASGN(hnorm t1, hnorm t2)
    | Term.PRINT(t1) -> Term.PRINT(hnorm t1)
    | Term.EQU (str, i, t1) -> Term.EQU (str, i,  hnorm t1)
    | Term.CLS(_,_,_) -> failwith "Not expected a clause in hnorm."
    | Term.PRED(str, t1) -> Term.PRED(str, hnorm t1)
    | Term.TENSOR (t1, t2) -> Term.TENSOR (hnorm t1, hnorm t2)
    | Term.LOLLI (str, t1, t2) -> Term.LOLLI (hnorm str, hnorm t1, hnorm t2)
    | Term.BANG (str, t1) -> Term.BANG (hnorm str, hnorm t1)
    | Term.HBANG (str, t1) -> Term.HBANG (hnorm str, hnorm t1)
    | Term.WITH (t1, t2) -> Term.WITH (hnorm t1, hnorm t2)
    | Term.PLUS (t1,t2) -> Term.PLUS (hnorm t1, hnorm t2)
    | Term.MINUS (t1,t2) -> Term.MINUS (hnorm t1, hnorm t2)
    | Term.TIMES (t1,t2) -> Term.TIMES (hnorm t1, hnorm t2)
    | Term.DIV (t1,t2) -> Term.DIV (hnorm t1, hnorm t2)
    | Term.ABS(_,n,t) -> Term.lambda n (hnorm t)
    | Term.FORALL(str,n,t) -> Term.FORALL(str,n,hnorm t)
    | Term.NEW(str,t) -> Term.NEW(str,hnorm t)
    | Term.BRACKET (t) -> Term.BRACKET(hnorm t)
    | Term.APP(t,args) ->
        let t = hnorm t in
          begin match Term.observe t with
            | Term.ABS(_, n,t) ->
                let e, n', args' = make_env n args in
                let ol = List.length e in
                  if n' > 0
                  then hnorm (Term.susp (Term.lambda n' t) ol 0 e)
                  else hnorm (Term.app (Term.susp t ol 0 e) args')
            (*| _ -> Term.app t args*)
            | _ -> Term.app t (List.map hnorm args) (*VN: Replaced this code from the orginal one in Bedwyr. It seems to make more sense.*)
          end
    | Term.SUSP(t,ol,nl,e) ->
        let t = hnorm t in
          begin match Term.observe t with
            (*| Term.NB _ *)
            | Term.CONS _ (*| Term.LIST _*) | Term.STRING _ | Term.INT _ 
            | Term.TOP | Term.ONE | Term.VAR _ -> t
            | Term.DB i ->
                if i > ol then
                  (* The index points to something outside the suspension *)
                  Term.db (i-ol+nl)
                else
                  (* The index has to be substituted for [e]'s [i]th element *)
                  begin match List.nth e (i-1) with
                    | Term.Dum l -> Term.db (nl - l)
                    | Term.Binding (t,l) -> hnorm (Term.susp t 0 (nl-l) [])
                  end
            | Term.ABS(_,n,t) ->
                Term.lambda n (hnorm (Term.susp t (ol+n) (nl+n)
                                       (add_dummies e n nl)))
            | Term.FORALL(str,n,t) ->
                Term.FORALL (str, n, hnorm (Term.susp t (ol+1) (nl+1)
                                       (add_dummies e 1 nl)))
            | Term.NEW(str,t) ->
                Term.NEW (str, hnorm (Term.susp t (ol+1) (nl+1)
                                       (add_dummies e 1 nl)))
            | Term.APP(t,args) ->
                let wrap x = Term.susp x ol nl e in
                  hnorm (Term.app (wrap t) (List.map wrap args))
            | Term.PRED (str, t1) -> Term.PRED(str, hnorm (Term.susp t1 ol nl e))
            | Term.COMP (cmp, t1,t2) -> Term.COMP(cmp, hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | Term.ASGN (t1,t2) -> Term.ASGN(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | Term.PRINT (t1) -> Term.PRINT(hnorm (Term.susp t1 ol nl e))
            | Term.EQU (str, i,t1) -> Term.EQU(str, i, hnorm (Term.susp t1 ol nl e))
            | Term.TENSOR (t1,t2) -> Term.TENSOR(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | Term.LOLLI (str, t1,t2) -> Term.LOLLI( hnorm (Term.susp str ol nl e), hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | Term.BANG (str, t1) -> Term.BANG(hnorm (Term.susp str ol nl e), hnorm (Term.susp t1 ol nl e))
            | Term.HBANG (str, t1) -> Term.HBANG(hnorm (Term.susp str ol nl e), hnorm (Term.susp t1 ol nl e))
            | Term.WITH (t1,t2) -> Term.WITH(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
	    | Term.BRACKET (f) -> Term.BRACKET(hnorm (Term.susp f ol nl e))
            | Term.CLS(typ,t1,t2) -> Term.CLS(typ,hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | Term.PLUS (t1,t2) -> Term.PLUS(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | Term.MINUS (t1,t2) ->  Term.MINUS(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | Term.TIMES (t1,t2) ->  Term.TIMES(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | Term.DIV (t1,t2) ->  Term.DIV(hnorm (Term.susp t1 ol nl e), hnorm (Term.susp t2 ol nl e))
            | Term.SUSP _ -> hnorm (Term.susp (hnorm t) ol nl e)
            | Term.PTR _ -> assert false
          end
    | Term.PTR _-> Term.print_term term; assert false

let rec deep_norm t =
  let t = hnorm t in
    match Term.observe t with
      (*| Term.NB _ *)
      | Term.CONS _
      (*| Term.LIST _*)
      | Term.STRING _
      | Term.INT _ | Term.ONE | Term.TOP | Term.CUT
      | Term.VAR _ | Term.DB _ -> t
      | Term.ABS (_,n,t) -> Term.lambda n (deep_norm t)
      | Term.APP (a,b) ->
            begin match Term.observe a with
              | Term.VAR _ 
              (*| Term.NB _ *)
              | Term.DB _ ->
                    Term.app a (List.map deep_norm b)
              | _ -> deep_norm (Term.app (deep_norm a) (List.map deep_norm b))
            end
      | Term.PRED (str,t1) -> Term.PRED (str, deep_norm t1)
      | Term.EQU (str, i, t1) -> Term.EQU (str, i, deep_norm t1)
      | Term.COMP (cmp, t1,t2) -> Term.COMP (cmp,deep_norm t1, deep_norm t2)
      | Term.ASGN (t1,t2) -> Term.ASGN (deep_norm t1, deep_norm t2)
      | Term.PRINT (t1) -> Term.PRINT (deep_norm t1)
      | Term.TENSOR (t1,t2) -> Term.TENSOR (deep_norm t1, deep_norm t2)
      | Term.LOLLI (str, t1,t2) -> Term.LOLLI (deep_norm str, deep_norm t1, deep_norm t2)
      | Term.BANG (str,t1) -> Term.BANG (deep_norm str, deep_norm t1)
      | Term.HBANG (str,t1) -> Term.HBANG (deep_norm str, deep_norm t1)
      | Term.WITH (t1,t2) -> Term.WITH (deep_norm t1, deep_norm t2)
      | Term.FORALL (str, i, t1) -> Term.FORALL (str, i, deep_norm t1)
      | Term.NEW (str, t1) -> Term.NEW (str, deep_norm t1)
      | Term.BRACKET (f) -> Term.BRACKET(deep_norm f)
      | Term.CLS (typ, t1, t2) -> Term.CLS (typ, deep_norm t1, deep_norm t2)
      | Term.PLUS (t1,t2) -> Term.PLUS (deep_norm t1, deep_norm t2)
      | Term.MINUS (t1,t2) -> Term.MINUS (deep_norm t1, deep_norm t2)
      | Term.TIMES (t1,t2) -> Term.TIMES (deep_norm t1, deep_norm t2)
      | Term.DIV (t1,t2) -> Term.DIV (deep_norm t1, deep_norm t2)
      | Term.PTR _ 
      | Term.SUSP _ -> assert false
