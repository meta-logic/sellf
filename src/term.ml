(* Things to do still:
Enable the user to insert the polarity of atoms;
Add connective to create Subexponentials
 *)

type 'a option = NONE | SOME of 'a

(* Each logical variable is identified by this number. 
 * A new logical variable should increment one in this identifier. *)
let varid = ref 0 ;;

(*Type for the types of terms. The user can define a kind, which is a basic 
type, or use the pre-defined types such as for integers, lists and predicates, 
composing them using the ->.*)
type types =
| TBASIC of basicTypes
| ARR of types * types (* type node *)
and basicTypes =
| TKIND of string (* Kind names *)
| TINT            (* Int type *)
| TSTRING
| TPRED           (* Predicate type "o" *)
| TSUBEX
| TLIST of basicTypes

(* VN: How to construct list of lists? *)
(* G: Maybe use the already built-in type list of OCaml *)


(*The definition of terms. They are basically simple lambda terms 
with some datatypes, such as integers, lists, and strings.*)
(*type listElement = 
(*Type of elements in a list: variables, integers, constants, strings.*)
(*We might want to eliminate completely lists from our language. It seems to cause
undesired complications without accomplishing much to our main goal.*)
| LVAR of string * int * tag
| LINT of int
| LCON of string
| LSTRING of string
| LAPP of listElement * listElement
and
lists = 
| LNIL
| LCONS of listElement * lists*)

(*Propositions are atoms, equalities, and logical connectives.*)
type terms = 
| PRED of string * terms (* G: name of the predicate (string) and head (terms) *)
| EQU of string * int * terms (* G: equality *)
| TOP
| ONE
| COMP of compType * terms * terms
| CUT
| TENSOR of terms * terms
| LOLLI of terms * terms * terms
| BANG of terms * terms
| HBANG of terms * terms
| WITH of terms * terms
| FORALL of string * int * terms
| CLS of clType * terms * terms
| VAR of var
| DB of int                         (*This seems necessary for head normalization procedure.*)
| INT of int
| CONS of string
| STRING of string
(*| LIST of lists*)
| APP of terms * terms list
| ABS of string * int * terms
| PLUS  of terms * terms
| MINUS of terms * terms
| TIMES of terms * terms 
| DIV of terms * terms
| SUSP of terms * int * int * env
| PTR  of ptr
| NEW of string * terms
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
EIG | CONST  | LOG
and 
var = {
  str : string;
  id  : int ; (* Only used for hashing *)
  tag : tag ;
  ts  : int ; (* Always zero for constants in Bedwyr *)
  lts : int
}

(* Four types of subexponentials described by a string *)
type subexp = 
| UNB (* unbounded: contraction and weakening *)
| AFF (* affine: weakening *)
| REL (* relevant: contraction *)
| LIN (* linear *)

let fVarC x = match x with
| "$test" -> 10
| _ -> 0;;

let varName x y = "$"^x^(string_of_int y);;

let print_compType ct = match ct with
    | EQ -> print_string " = "
    | LESS -> print_string " < "
    | GEQ -> print_string " >= "
    | GRT -> print_string " > "
    | LEQ -> print_string " <= "
    | NEQ -> print_string " <> "

let print_type_cls ty = match ty with 
    | DEF -> print_string " DEF "
    | LOL -> print_string " LOL "

let rec print_term term = match term with 
  | VAR v -> if v.tag = EIG then (print_string v.str; print_string "EIG_"; print_int v.id) else (print_string v.str;print_string "LOG_"; print_int v.id)
  | DB (i) -> print_string "_DB"; print_int i
  | INT (x) -> print_int x
  | CONS (x) -> print_string x
  | STRING (x) -> print_string x
  | APP (x, y) -> let n = List.length y in 
    let rec print_app_lists lst = 
    begin 
        match lst with
        | [] -> ()
        | t :: body -> print_term t; print_string ")"; print_app_lists body
    end in 
    for i = 1 to n do 
    print_string "("
    done; 
    print_term x; print_string " "; print_app_lists y
  | ABS (x, i, y) -> print_string "(/lam"; print_string x; print_int i; print_string " "; print_term y; print_string ")"
  | PLUS (ib1, ib2) -> print_term ib1; print_string " + "; print_term ib2
  | MINUS (ib1, ib2) -> print_term ib1; print_string " - "; print_term ib2
  | TIMES (ib1, ib2) -> print_term ib1; print_string " * "; print_term ib2
  | DIV (ib1, ib2) -> print_term ib1; print_string " / "; print_term ib2
  | SUSP (t, ol, nl, env) -> (*print_string "SUSP";*) 
                begin
                  match t with 
                  | DB i ->
                    begin 
                      match List.nth env (i-1) with 
                      | Binding(t_bind, j) ->  print_term t_bind
                      | _ -> print_term t
                    end
                  | _ -> print_term t
                end
  | PTR {contents = T t} ->  (*print_string "PTR";*)print_term t
  | PTR {contents = V v} ->  (*print_string "PTR";*)print_term (VAR v)
  | PRED (s, t) -> print_term t
  | EQU (s, i, t) -> print_string (" eq prop "); print_term t; print_int i
  | TOP -> print_string "top"
  | ONE -> print_string "one"
  | COMP (c, i1, i2) -> print_term i1; print_compType c; print_term i2
  | CUT -> print_string "fail(cut)"
  | TENSOR (t1, t2) -> print_term t1; print_string " , "; print_term t2
  | LOLLI (s, t1, t2) -> print_term t1; print_string (" ["); print_term s; print_string("] o- "); print_term t2
  | BANG (s, t) -> print_string (" ["); print_term s; print_string("]! "); print_term t
  | HBANG (s, t) -> print_string (" ["); print_term s; print_string("]^! "); print_term t
  | WITH (t1, t2) -> print_term t1; print_string " & "; print_term t2
  | FORALL (s, i, t) -> print_string ("V "^s^(string_of_int i)^" "); print_term t
  | CLS (ty, t1, t2) -> print_term t1; print_type_cls ty; print_term t2
  | NEW (s, t) -> print_string ("new"^"/lam"^s); print_term t

let rec print_list_terms args = 
   match args with
  | [] -> ()
  | term1 :: body -> print_term term1; print_string " -- "; print_list_terms body

let rec print_basicType btyp = match btyp with
	| TKIND (x) -> print_string x
	| TINT -> print_string "int"
	| TSTRING -> print_string "string"
	| TPRED -> print_string "o"
  | TSUBEX -> print_string "tsub"
	| TLIST (x) -> print_string "(list "; print_basicType x; print_string ")"

let rec print_type typ = match typ with 
	| TBASIC (x) -> print_basicType x
	| ARR (x,y) -> match x with
                       | TBASIC _ ->  print_type x; print_string " -> "; print_type y
                       | _ -> print_string "("; print_type x; print_string ")"; print_string " -> "; print_type y
let notInTbl hash entry = 
	let l = (Hashtbl.find_all hash entry) in
	   if List.length l == 0 then NONE           (* kind not in table*)
       else SOME (entry)       		             (* kind in table *)

let addKTbl hash entry = 
	match entry with
	| TINT -> NONE
	| TPRED -> NONE
	| TKIND (k) -> (match (notInTbl hash k) with
		        | NONE -> Hashtbl.add hash k (TKIND (k)); 
			       print_string (" New kind "^k^" created.\n"); flush stdout; 
			       NONE
			| SOME (k1) -> SOME (k1))
	| _ -> NONE
;;

let rec tCheckAuxList term = TINT

(* Hashtable with the kind *)
let kTbl = Hashtbl.create 100 ;;
(* Hashtable with the types*)
let tTbl = Hashtbl.create 100 ;;
(* Hashtable with the rules*)
let rTbl = Hashtbl.create 100 ;;

(* Need to add "o" as a pre-defined kind *)
Hashtbl.add kTbl "o" (TPRED);;
(* Example of a type *)
Hashtbl.add tTbl "$example" (ARR ( TBASIC (TINT), TBASIC (TINT) ));;
(* Example of a rule: $example :- 1.   *)
Hashtbl.add rTbl "$example" (CLS (DEF, PRED ("$example", CONS ("$example")), ONE ) );;

let addTTbl hash name entry = 
	Hashtbl.add hash name entry;
	print_string (" New type created: "^name^" : "); print_type entry; print_newline(); flush stdout
;; 

(*Function that takes a term and returns a pair with the head of the term and the list of arguments.*)
let rec term2list term = 
let rec num_arg t = match t with
  | APP (t1, t2) -> 1 + (num_arg t1)
  | _ -> 0
in
let rec term2listaux term n =
  if n > 0 then 
  begin
    match term with
    | APP(t1, t2) -> let (head, args) = (term2listaux t1 (n-1)) in 
         (head, List.append  args [t2] )  
    | _ -> failwith "ERROR: Expected an application when transforming a term into a list of terms."
  end
  else (term, [])
in
let n = num_arg term in 
term2listaux term n

(*Function that receives a head and a list of arguments and transforms it to a term.*)
let rec list2term head args = 
  match args with
  | [] ->  head
  | term1 :: body -> list2term (APP(head, term1)) body

let rec eq t1 t2 =
  match t1,t2 with
    (* Compare leafs *)
    | DB i1, DB i2 -> i1 = i2
   (* | NB i1, NB i2 -> i1=i2*)
    | PTR {contents=V v1}, PTR {contents=V v2} -> v1==v2
    (* Ignore Ptr. It's an implementation artifact *)
    | _, PTR {contents=T t2} -> eq t1 t2
    | PTR {contents=T t1}, _ -> eq t1 t2
    (* Propagation *)
    | APP (h1,l1), APP (h2,l2) ->
        List.length l1 = List.length l2 &&
        List.fold_left2
          (fun test t1 t2 -> test && eq t1 t2)
          true (h1::l1) (h2::l2)
    | ABS (_,n,t1), ABS (_,m,t2) -> n = m && eq t1 t2
    | VAR _, _ | _, VAR _ -> assert false
    | SUSP (t,ol,nl,e), SUSP (tt,oll,nll,ee) ->
        ol = oll && nl = nll && eq t tt &&
          List.fold_left2
            (fun test e1 e2 ->
               test && match e1,e2 with
                 | Dum i, Dum j when i = j -> true
                 | Binding (t,i), Binding (tt,j) when i=j && eq t tt -> true
                 | _ -> false)
            true e ee
    | _ -> false


let rec observe = function
  | PTR {contents=T d} -> observe d
  | PTR {contents=V v} -> VAR v
  | t -> t

let rec deref = function
  | PTR {contents=T t} -> deref t
  | t -> t

let lambda n t =
  assert (n>=0) ;
  if n=0 then t else
    let rec aux n t =
      match t with
        | ABS (_,n',t') -> aux (n+n') t'
        | _ -> ABS ("_",n,t)
    in
      aux n t


let susp t ol nl e = SUSP (t,ol,nl,e)

(*let rec app a b = list2term a b*)

let app a b = if b = [] then a else match observe a with
  | APP(a,c) -> APP (a,c @ b)
  | _ -> APP (a,b)

let db n = DB n

let rec remove_abs clause = 
  match clause with
    | ABS (str, i, t) -> remove_abs t
    | _ -> clause

(*Function that assigns de Bruijn numbers to variables.*)
let rec deBruijn_aux flag fVarC nABS body =   
  match body with
  | VAR v  ->
    begin
      match (fVarC v.str) with
        | (id, _, 0) -> (*VN: Case when the variable is bounded by a FORALL*)
             let (idNew, _, _ ) = fVarC v.str in
             let v2 = {str = v.str; id = idNew; tag = v.tag; ts = v.ts; lts = v.lts} in VAR v2
        | (id, nABS1, 1) -> (*VN: Case when the variable is bounded by an abstraction*) 
           if flag then DB(id + nABS1) 
           else let (idNew, _, _ ) = fVarC v.str in
             let v2 = {str = v.str; id = idNew; tag = v.tag; ts = v.ts; lts = v.lts} in VAR v2
        | _ -> failwith "Impossible case reached in the De Bruijn Auxiliary."
    end
   (*| LIST (lists) -> LIST (deBruijnList lists fVarC)*)
  | APP (term1, term2) -> 
     APP (deBruijn_aux flag fVarC nABS term1, List.map (deBruijn_aux flag fVarC nABS) term2)
  | ABS (str, i, body1) -> 
     let fVarCNew x = 
     begin match x with
       | x when x = str ->  (1, 0, 1)
       | x -> let (id, nABS_rest, tABS) = fVarC x in (id, nABS_rest + 1, tABS)
     end
     in ABS (str, 1, deBruijn_aux flag fVarCNew (nABS + 1) body1)
  | PLUS (int1, int2) -> PLUS (deBruijn_aux flag fVarC nABS int1, deBruijn_aux flag fVarC nABS int2)
  | MINUS (int1, int2) -> MINUS (deBruijn_aux flag fVarC nABS int1, deBruijn_aux flag fVarC nABS int2)
  | TIMES (int1, int2) -> TIMES (deBruijn_aux flag fVarC nABS int1, deBruijn_aux flag fVarC nABS int2) 
  | DIV (int1, int2) -> DIV (deBruijn_aux flag fVarC nABS int1, deBruijn_aux flag fVarC nABS int2)
  | TENSOR (body1, body2) -> TENSOR (deBruijn_aux flag fVarC nABS body1, deBruijn_aux flag fVarC nABS body2)
  | LOLLI (sub, body1, body2) -> LOLLI (deBruijn_aux flag fVarC nABS sub, deBruijn_aux flag fVarC nABS body1, deBruijn_aux flag fVarC nABS body2)
  | BANG (sub, body1) -> BANG (deBruijn_aux flag fVarC nABS sub, deBruijn_aux flag fVarC nABS body1) 
  | HBANG (sub, body1) -> HBANG (deBruijn_aux flag fVarC nABS sub, deBruijn_aux flag fVarC nABS body1) 
  | WITH (body1, body2) -> WITH (deBruijn_aux flag fVarC nABS body1, deBruijn_aux flag fVarC nABS body2)
  | FORALL (str, _, body1) -> 
     let fVarCNew x = 
     begin match x with
       | x when x = str ->  (1, 0, 1)
       | x -> let (id, nABS_rest, tABS) = fVarC x in (id, nABS_rest + 1, tABS)
     end
     (*let (idOld, nABS, tABS) =  fVarC str in
  			let fVarCNew x = (match x with
       | x when x = str ->  (idOld + 1, nABS, 0)
       | x -> fVarC x)*)
  			(*in FORALL(str, idOld, deBruijn_aux flag fVarCNew nABS body1)*)
     in FORALL (str, 1, deBruijn_aux flag fVarCNew (nABS + 1) body1)
  | NEW (str, body1) -> 
     let fVarCNew x = 
     begin match x with
       | x when x = str ->  (1, 0, 1)
       | x -> let (id, nABS_rest, tABS) = fVarC x in (id, nABS_rest + 1, tABS)
     end
     (*let (idOld, nABS, tABS) =  fVarC str in
        let fVarCNew x = (match x with
       | x when x = str ->  (idOld + 1, nABS, 0)
       | x -> fVarC x)*)
        (*in FORALL(str, idOld, deBruijn_aux flag fVarCNew nABS body1)*)
     in NEW (str, deBruijn_aux flag fVarCNew (nABS + 1) body1)
  | PRED (srt, terms) ->  PRED (srt, deBruijn_aux flag fVarC nABS terms)
  | EQU (str, _, terms) -> 
     let (id, nABS, tABS) =  fVarC str in 
     EQU (str, id, deBruijn_aux flag fVarC nABS terms)
  | CLS(tp, t1, t2) -> CLS(tp, deBruijn_aux flag fVarC nABS t1, deBruijn_aux flag fVarC nABS t2)
  | COMP(comp, t1, t2) -> COMP(comp, deBruijn_aux flag fVarC nABS t1, deBruijn_aux flag fVarC nABS t2)
  | x -> x

let rec collect_free_variables clause =
  let rec collect_free_variables_list freeVar bVar lst = 
    begin
      match lst with
      | [t] -> collect_free_variables_aux freeVar bVar t
      | t :: body ->  
          let freeVar1 = collect_free_variables_aux freeVar bVar t in 
          collect_free_variables_list freeVar1 bVar body
    end
  and
  collect_free_variables_aux freeVar bVar clause = 
    begin
      match observe clause with
        | VAR v  when List.mem v.str freeVar || List.mem v.str bVar-> freeVar
        | VAR v  -> v.str :: freeVar
        | PRED(_, t1) -> collect_free_variables_aux freeVar bVar t1
        | TOP | ONE | CUT | DB _ | INT _ | CONS _ | STRING _ | SUSP _ -> freeVar
        | EQU(_, _, t1)  -> collect_free_variables_aux freeVar bVar t1
        | FORALL(str, _, t1) | ABS(str, _, t1) | NEW (str, t1) -> collect_free_variables_aux freeVar (str :: bVar) t1
        | APP(t1, t2) -> let freeVar1 = collect_free_variables_aux freeVar bVar t1 in
                                collect_free_variables_list freeVar1 bVar t2 
        | DIV (t1, t2)  | TIMES (t1, t2) | MINUS (t1, t2) | PLUS (t1, t2) 
        | TENSOR(t1, t2) | COMP(_, t1, t2) | WITH(t1,t2) | CLS(_, t1, t2) | BANG(t1, t2) | HBANG(t1, t2) -> 
          let freeVar1 = collect_free_variables_aux freeVar bVar t1 in 
          let freeVar2 = collect_free_variables_aux freeVar1 bVar t2 in 
          freeVar2
        | LOLLI (subex, t1, t2)  -> 
          let freeVar1 = collect_free_variables_aux freeVar bVar subex in 
          let freeVar2 = collect_free_variables_aux freeVar1 bVar t1 in
          let freeVar3 = collect_free_variables_aux freeVar2 bVar t2 in
            freeVar3
    end
  in 
  collect_free_variables_aux [] [] clause

(*VN: This function introduces deBruijn indices to a raw clause parsed. However, there are two 
modes according to flag. When flag is true then in the clause returned the variables binded
by an abstraction are replaced by DBs. When flag is false, these variables are not replaced. 
One should use flag = false when one wants to typecheck a term and use flag=true, when 
one wants a term that normalizes. *)
let deBruijn flag clause = 
  let rec add_abstractions freeVar clause = 
   begin 
    match freeVar with
    | [] ->  clause
    | t::body -> ABS(t, 1, add_abstractions body clause)
  end in
  let freeVar = collect_free_variables clause in
  (*let _ = List.iter print_string freeVar in*)  
  let clause_abs = add_abstractions freeVar clause in
  let fVarCInit x = (match x with 
    | "$example" -> (0,0,0)
    | _ -> (0,0,0))
  in if flag then deBruijn_aux flag fVarCInit 0 clause_abs 
  else deBruijn_aux flag fVarCInit 0 clause

(*VN: Still have to check for occurchecks.*)

(* Function for unifying types. It returns a substitution with the unification. In the 
case that the types are not unifyable, then the function fails with an error. 
Here we assume that type variables are defined as a kind.*)
let rec unifyTypes gTyp vTyp sub = match (gTyp, vTyp) with 
		| (ARR (x1, y1), ARR (x2, y2)) -> let sub2 = unifyTypes x1 x2 sub in 
						  (unifyTypes y1 y2 sub2)
		| (TBASIC (TINT), TBASIC (TINT)) -> sub
    | (TBASIC (TSUBEX), TBASIC (TSUBEX)) -> sub
		| (TBASIC (TSTRING), TBASIC (TSTRING)) -> sub
		| (TBASIC (TPRED), TBASIC (TPRED)) -> sub
		(*VN: Not exhaustive yet. Waiting for a better implem. for lists*)
		(*| (TBASIC (TLIST(TINT)), TBASIC (TLIST(TINT))) -> sub *)
		| (x, TBASIC (TKIND (y))) -> (match sub (TBASIC (TKIND (y))) with
			  		| NONE ->  let sub2 z = (match z with
			  					| TBASIC (TKIND (d)) when d = y ->  SOME (x)  (* *)
								| d -> sub d)
						   in sub2
					| SOME (x1) when x1 = x -> sub
					| SOME (_) -> failwith "Failed when unifying type variables.")
		| _ -> print_string" Type1:"; print_type gTyp; print_string "  Type2:"; print_type vTyp; 
             print_newline; failwith "Failed when unifying type variables:"

(* Function that applies a substitution eagerly to a type. *)
let rec applySub sub typ = match typ with 
			   | ARR (t0, t1) -> ARR (applySub sub t0, applySub sub t1)
			   | x -> (match sub x with
				  | NONE -> typ
				  | SOME (t) -> (match sub t with
						| NONE -> t
						| _ -> applySub sub t))
 
(*Function that typechecks a term. It takes a term, possibly with variables, a type, a subsitution for the 
type variables, an environment that given a term variable returns its type, and a number varC with the 
number of the type variables used. *)
let rec tCheckAux term typ sub env varC = 
(*Initialize the substitution for type variables as empty*)
let subInit x = (match x with 
		  | _ -> NONE) 
in 
(*All variables appearing in a comparison must have type int.*)
let rec tCheckInt intBody env = 
match intBody with
   | INT (x) -> (subInit, env)
   | VAR v -> (match env (v.str,v.id) with 
   		     | NONE -> let env2 z = (match z with
		     				| (x1,i1) when (x1,i1) = (v.str,v.id) -> SOME (TBASIC(TINT))
		     				| (x1,i1) -> env (x1,i1)) 
		       in (subInit, env2)
		     | SOME (TBASIC(TINT)) -> (subInit, env)
		     | SOME (_) -> failwith ("Error: Variable  "^v.str^" does not have type INT in a comparison."))
   | PLUS (int1, int2) -> let (_,env1) = tCheckInt int1 env in
	 		   let (_,env2) = tCheckInt int2 env1 in (subInit, env2)
   | MINUS (int1, int2) -> let (_,env1) = tCheckInt int1 env in
	  		        let (_,env2) = tCheckInt int2 env1 in (subInit, env2)
   | TIMES (int1, int2) -> let (_,env1) = tCheckInt int1 env in
				let (_,env2) = tCheckInt int2 env1 in (subInit, env2)
   | DIV (int1, int2) -> let (_,env1) = tCheckInt int1 env in
				let (_,env2) = tCheckInt int2 env1 in (subInit, env2) 
   | _ -> failwith "Error: Invalid term in a comparison."
in
match term with 
(*Typecheck terms and at the same time updating the environment and substitution functions.*)
	| INT (x) -> ((TBASIC (TINT)), unifyTypes (TBASIC (TINT)) typ sub, env, varC)
	| STRING (x) -> ((TBASIC (TSTRING)), unifyTypes (TBASIC (TSTRING)) typ sub, env, varC)
	(*VN: Not exhaustive yet. Waiting for a better implem. for lists*)
	(*| LIST (x) -> ((TBASIC (TLIST(TINT))), unifyTypes (TBASIC (TLIST(TINT))) typ sub, env, varC) *)
	| CONS (x) -> 
      begin
      try 
        let typC = Hashtbl.find tTbl x in (typC, unifyTypes typC typ sub, env, varC)
      with
       | Not_found -> let typC = TBASIC(TSUBEX) in 
                              (typC, unifyTypes typC typ sub, env, varC)
      end
	| VAR v -> let (x, y) = (v.str, v.id) in 
      (match env (x,y) with
			| NONE -> let env2 z = (match z with
					     | (x1,y1) when (x1,y1) = (x,y) -> SOME (typ)
					     | (x1,y1) -> env (x1,y1))
				in (typ, sub, env2, varC)
			| SOME (typ2) -> let sub2 = unifyTypes typ2 typ sub in
					 let newTyp = applySub sub2 typ in  
					 let env2 z = (match z with
					     | (x1,y1) when (x1,y1) = (x,y) -> SOME (newTyp)
					     | (x1,y1) -> env (x1,y1))
					 in 
					 (newTyp, sub2, env2, varC))
  | ABS (x, y, term2) -> (match typ with
      | ARR(t1, t2) -> (match env (x,y) with
          | NONE -> let env2 z = (match z with
               | (x1,y1) when (x1,y1) = (x,y) -> SOME (t1)
               | (x1,y1) -> env (x1,y1))
               in tCheckAux term2 t2 sub env2 varC
          | SOME (typ2) -> let sub2 = unifyTypes typ2 typ sub in
              let newTyp = applySub sub2 typ in  
              let env2 z = (match z with
                  | (x1,y1) when (x1,y1) = (x,y) -> SOME (newTyp)
                  | (x1,y1) -> env (x1,y1))
              in 
              tCheckAux term2 t2 sub2 env2 varC)
      | _ -> print_type typ; failwith " Expected an arrow type.")
	| APP (head, body) -> 
      (*VN: Construct an arrow type for all body elements with type variables.*)
      let rec construct_type_arr args endType varC = 
        begin
          match args with
            | [] -> (endType, varC)
            | t :: body -> 
              let (rTyp, varCup) = construct_type_arr body endType (varC+1)
              in
              let lTyp = TBASIC (TKIND (varName "typeVar" varC))
              in (ARR(lTyp, rTyp), varCup)
        end
      in
      (*VN: Typecheck and unify types of the elements of the body.*)
      let rec construct_type_args args typ sub1 env1 varC =
        begin
          match args, typ with
          | [t], ARR(t1, tHead) -> let (t2, sub2, env2, varC2) = tCheckAux t t1 sub env (varC + 1) in
                    (*print_string " Term: "; print_term t; print_string " Type input: ";
                    print_type newType; print_string " Type output: ";
                    print_type t2; print_string "\n";*)
                    (ARR(t2, tHead), sub2, env2, varC2)
          | tr::body, ARR(t1, t2) -> 
            let (t3, sub2, env2, varC2) = tCheckAux tr t1 sub env (varC + 1) in
            let (t4, sub3, env3, varC3) = construct_type_args body t2 sub2 env2 varC2 
            in (ARR(t3,t4), sub3, env3, varC3)
        end
      in
      (*VN: First cosntruct the arrow type with type variables.*)
      let (builtType, varC1) = construct_type_arr body typ varC 
      in
      (*VN: Type check the head of the application using the arrow type created.*)
      let (t_head, sub_head, env_head, varC_head) = tCheckAux head builtType sub env varC1
      in
      (*VN: Typecheck the body elements of the application.*)
      let (t_final, sub_final, env_final, varC_final) =  construct_type_args body t_head sub_head env_head varC_head 
      in
      (*VN: Return the type instantiated with the substitution computed.*)
        ((applySub sub_final t_final), sub_final, env_final, varC_final)
(*Arithmetic comparisons do not require type variables since everything is integer, hence the value 0*)
  | PLUS (int1, int2) -> let (_,env1) = tCheckInt int1 env in
	 		        let (_,env2) = tCheckInt int2 env1 in (TBASIC(TINT), subInit, env2, 0)
	| MINUS (int1, int2) -> let (_,env1) = tCheckInt int1 env in
	  		        let (_,env2) = tCheckInt int2 env1 in (TBASIC(TINT), subInit, env2, 0)
	| TIMES (int1, int2) -> let (_,env1) = tCheckInt int1 env in
				let (_,env2) = tCheckInt int2 env1 in (TBASIC(TINT), subInit, env2, 0)
	| DIV (int1, int2) -> let (_,env1) = tCheckInt int1 env in
				let (_,env2) = tCheckInt int2 env1 in (TBASIC(TINT), subInit, env2, 0)
  | _ -> failwith "Error: Encountered a Susp term when typechecking a term."


 (* Functions that grounds the image of an environment, so that the type variables created in the 
unification process are eliminated. Usually this function is called when moving from typechecking one predicate 
to the next one. In the process, we want that the image of the environment does not mention any type 
variables created, so that one can reset the type variable counter.*)
let rec grEnvImgTerms sub env terms = match terms with
				| VAR v -> let (x,i) = (v.str, v.id) in
          let env2 z = (match z with
					| (x1,i1) when (x1,i1) = (x,i) -> 
            begin
              match env (x1,i1) with
              | SOME (t) -> SOME (applySub sub t)
              | _ -> NONE
            end
					| (x1,i1) -> env (x1,i1)) in env2
				| APP (x, y) -> 
            let rec grListTerms sub env lst = 
            begin
              match lst with
                | [t] -> grEnvImgTerms sub env t
                | t :: body -> let envT = grEnvImgTerms sub env t in 
                                    grListTerms sub envT body
                | [] -> failwith "ERROR: Encountered an application with no body terms when grounding environment."
            end in
            let env2 = grEnvImgTerms sub env x in 
						grListTerms sub env2 y
				| _ -> env

let rec grEnvImgProp sub env prop = match prop with
		| PRED (_, terms) -> grEnvImgTerms sub env terms
		| _ -> env


(*Main function used to typecheck a clause.*)
let rec typeCheck clause = 
	let subInit x = (match x with 
		 	_ -> NONE) in 
	let envInit x = (match x with 
		 	_ -> NONE) in
	let rec tCheckBody body env = 
    begin match body with
      | PRED(_, x) -> let (_, s, e, _) = tCheckAux x (TBASIC (TPRED)) subInit env 0
            in let e2 = grEnvImgTerms s e x
                in (s, e2) 
      | TOP -> (subInit, env)
      | ONE -> (subInit, env)
      | CUT -> (subInit, env)
      | EQU (x, i, y) -> let newType = TBASIC (TKIND (varName "typeVar" 0)) in
          let (typeY, subY, envY, varC) = tCheckAux y newType subInit env 1
          in 
          begin
            match envY (x,i) with
            | NONE -> let env2 z = 
                begin match z with
                  | (x1,i1) when (x1,i1) = (x,i) -> SOME (typeY)
                  | (x1,i1) -> envY (x1,i1)
                end
              in (subY, env2)
            | SOME (typeY1) when typeY1 = typeY -> (subY,envY)
            | SOME (_) -> failwith "Error: Type variable mismatched"
          end
      | COMP (_, int1, int2) -> let (_,_,env1,_) = tCheckAux int1 (TBASIC (TINT)) subInit env 0
              in let (_,_,env2,_) = (tCheckAux int2 (TBASIC (TINT)) subInit env1 0)
              in (subInit, env2)
      | LOLLI (subexp, body1, body2) -> (*print_term (LOLLI (subexp, body1, body2));*)
              (*let (_,_,env1,_) = tCheckAux subexp (TBASIC(TSUBEX)) subInit env 0 in
              let (_,env2) = tCheckBody body1 env1 in*)
              tCheckBody body2 env
      | BANG (subexp, body1) -> 
              let (_,_,env1,_) = tCheckAux subexp (TBASIC(TSUBEX)) subInit env 0 in
              tCheckBody body1 env1
      | HBANG (subexp, body1) -> 
              let (_,_,env1,_) = tCheckAux subexp (TBASIC(TSUBEX)) subInit env 0 in
              tCheckBody body1 env1
      | TENSOR (body1, body2) -> let (sub2, env2) = tCheckBody body1 env in
              tCheckBody body2 env2
      | WITH (body1, body2) -> let (sub2, env2) = tCheckBody body1 env in
          tCheckBody body2 env2
      | FORALL (_, _, body1) -> tCheckBody body1 env
      | NEW (_, t) -> tCheckBody t env 
      (*VN: The following two cases are for when variables are of type o.*) 
      | VAR v ->  tCheckBody (PRED("", VAR v)) env
      | APP(head, args) -> tCheckBody (PRED("", APP(head, args))) env
      | _ -> print_term body; failwith " Expected a body element while typechecking."
    end
	in
	match clause with
	| CLS (_, head, body) -> let (sub, env2) = tCheckBody head envInit
				 in let envH = grEnvImgProp sub env2 head 
				 in  tCheckBody body envH
  | _ -> print_term clause; failwith " Expected a clause while typechecking."
  

module Hint = struct
  module M = Map.Make(struct type t = int let compare = compare end)
  let var_names = ref M.empty
  let add var name =
    var_names := M.add var.id name !var_names ;
    Gc.finalise (fun v -> var_names := M.remove v.id !var_names) var
  let find var =
    M.find var.id !var_names
end

let fresh_id =
  let c = ref 0 in
    fun () -> incr c ; !c

(** Generate a fresh variable, attach a naming hint to it. *)
let fresh ?name ~lts ~ts tag =
  let v = {str="_";id=fresh_id();tag=tag;ts=ts;lts=lts} in
    begin match name with
      | Some name -> Hint.add v name
      | None -> ()
    end ;
    PTR (ref (V v))

module NS = Map.Make(struct type t = string let compare = compare end)
type namespace = terms NS.t

(** [symbols] is used to obtain the exact same variable term for
  * representing all occurrences of that variable -- used by the parser. *)
let symbols = ref NS.empty

let save_namespace () = !symbols
let restore_namespace s = symbols := s

(** Get the unique variable attached to that name, preserving sharing.
  * The variable is created if it does not exist. *)
let get_var_by_name ~tag ~ts ~lts name =
  try
    NS.find name !symbols
  with
    | Not_found ->
        assert (name <> "") ;
        let lts = 0 in
        let t = fresh tag ~ts ~lts ~name in
          symbols := NS.add name t !symbols ;
          t

(* Same as [get_var_by_name] but infers the tag from the name and sets both
 * levels to 0. *)
let atom name =
  let tag = match name.[0] with
    | 'A'..'Z' -> LOG
    | _ -> CONST
  in
    get_var_by_name ~ts:0 ~lts:0 ~tag name

let get_var x = match observe x with
  | VAR v -> v
  | _ -> assert false

(** Raise Not_found if not naming hint is attached to the variable. *)
let get_hint v =
  let v = get_var v in
  try
    Hint.find v
  with
    | Not_found ->
        begin match v.tag with
          | LOG-> "H"
          | EIG -> "h"
          | CONST -> "c"
        end

(** Find an unique name for [v] (based on a naming hint if there is one)
  * and registers it in the symbols table. *)
let get_name var =
  let var = deref var in
  let existing_name =
    NS.fold
      (fun key value x ->
         (* Do NOT use [eq] instead of [=] here, otherwise it will follow
          * references -- notice that the term in the table has been changed by
          * bindings too.
          * Suppose you bind Y to 1,
          * the initial value representing Y would be [eq] to 1,
          * and could thus take the name 1, depending on the order in which the
          * table is traversed. *)
         if value = var then Some key else x)
      !symbols
      None
  in
    match existing_name with
      | Some n -> n
      | None ->
          let prefix = get_hint var in
          let rec lookup suffix =
            let name =
              if suffix < 0 then prefix else prefix ^ string_of_int suffix
            in
              if NS.mem name !symbols then
                lookup (suffix+1)
              else begin
                symbols := NS.add name var !symbols ;
                name
              end
          in
            lookup (-1)

let dummy = let n = -1 in PTR(ref(V {str="_"; id=n;ts=n;lts=n;tag=CONST }))

(** [get_dummy_name prefix] finds a free name starting with [prefix] and
  * registers it. If [start] is not provided, the attempted suffixes will be
  * "", "0", "1", etc. If it is provided it will be used as the first suffix to
  * try. *)
let get_dummy_name ?(start=(-1)) prefix =
  let rec lookup suffix =
    let name =
      if suffix < 0 then prefix else prefix ^ string_of_int suffix
    in
      if NS.mem name !symbols then
        lookup (suffix+1)
      else begin
        symbols := NS.add name dummy !symbols ;
        name
      end
  in
    lookup start

(** List of [n] new dummy names, most recent first. *)
let get_dummy_names ?(start=(-1)) n prefix =
  let rec aux i =
    if i=0 then [] else
      let tl = aux (i-1) in
        (get_dummy_name ~start prefix)::tl
  in
    List.rev (aux n)

let is_free name =
  not (NS.mem name !symbols)

let free n =
  symbols := NS.remove n !symbols

(** {1 Copying} *)

(** [copy ()] instantiates a copier, that copies terms,
  * preserving sharing inside the set of copied terms.
  * Input terms should be normalized. *)
let copy_eigen () =
  let tbl = Hashtbl.create 100 in
  fun ?(passive=false) tm ->
  let rec cp tm = match observe tm with
    | VAR v when v.tag = EIG ->
        begin try Hashtbl.find tbl v with
          | Not_found ->
              if passive then tm else
                let v' = { v with id = fresh_id () } in
                let x = PTR (ref (V v')) in
                  begin try Hint.add v' (Hint.find v) with _ -> () end ;
                  Hashtbl.add tbl v x ;
                  x
        end
    | VAR v -> tm
    | APP (a,l) -> APP (cp a, List.map cp l)
    | ABS (str,n,b) -> ABS (str, n, cp b)
    | DIV (t1,t2) -> DIV (cp t1, cp t2)
    | TIMES (t1,t2) -> TIMES (cp t1, cp t2)
    | MINUS (t1,t2) -> MINUS (cp t1, cp t2)
    | PLUS (t1,t2) -> PLUS (cp t1, cp t2)
    | STRING (t1) -> STRING (t1)
    | INT (t1) -> INT (t1)
    | CONS (t1) -> CONS (t1)
    (*| LIST (t1) -> LIST(t1)*)
    (*| NB i*) | DB i as x -> x
    | SUSP _ | PTR _ -> assert false
  in
    cp tm

(** {1 Convenience} *)

let string text = get_var_by_name ~tag:CONST ~lts:0 ~ts:0 text

let binop s a b = APP ((atom s),[a;b])

let db n = DB n

let app a b = if b = [] then a else match observe a with
  | APP(a,c) -> APP (a,c @ b)
  | _ -> APP (a,b)

let susp t ol nl e = SUSP (t,ol,nl,e)

let plus l = match l with
  | [t1;t2] -> PLUS(t1,t2)
  | _ -> failwith "ERROR: Expected two elements in a plus."

let minus l = match l with
  | [t1;t2] -> MINUS(t1,t2)
  | _ -> failwith "ERROR: Expected two elements in a plus."

let times l = match l with
  | [t1;t2] -> TIMES(t1,t2)
  | _ -> failwith "ERROR: Expected two elements in a times."

let div l = match l with
  | [t1;t2] -> DIV(t1,t2)
  | _ -> failwith "ERROR: Expected two elements in a times."


(*let get_nablas x =
  let rec nb l t = match observe t with
    | Var _ -> l
    | App (h,ts) -> List.fold_left nb (nb l h) ts
    | Lam (n,t') -> nb l t'
    | DB _ -> l
    | NB i -> if List.mem i l then l else i::l
    | Susp _ | Ptr _ -> assert false
  in
    nb [] x*)

module Notations =
struct
  let (%=) = eq
  let (!!) = observe
  let (//) = lambda
  let (^^) = app
end

let fresh_name name =
  let v = fresh ~name:name CONST ~lts:0 ~ts:0 in
  get_name v
