(**/**)
open Types
open Prints

(* Verbose on/off *)
let verbose = ref false ;;
(* Tabling on/off *)
let tabling = ref false ;;
(* Timer on/off *)
let time = ref false ;;
(* Bound for the proof search *)
let psBound = ref 1000 ;;

(* Each logical variable is identified by this number. 
 * A new logical variable should increment one in this identifier. *)
let varid = ref 0 ;;

(***** Extracts information from the specification of an object logic rule *****)

(* Returns the predicate in the head of a specification. 
 * TODO: if there are existential quantifiers, the DB indices are messed up with
 * this method... *)
let rec getHeadPredicate f = match f with 
  | TENSOR(NOT(prd), spc) -> prd
  | EXISTS(s, i, t) -> getHeadPredicate t
  | NOT(prd) -> prd
  | PRED(_, _, _) -> f
  | _ -> failwith ("No head: " ^ Prints.termToString f)
;;

(* Returns the side of the introduction rule *)
let rec getSide f = match getHeadPredicate f with 
  | PRED("lft", _, _) -> "l"
  | PRED("rght", _, _) -> "r"
  | PRED("mlft", _, _) -> "l"
  | PRED("mrght", _, _) -> "r"
  | _ -> failwith ("No side information available (predicate not corresponding to a specification's head or not a predicate): " ^ Prints.termToString f)
;;

let getConnectiveName f = match getHeadPredicate f with
  | PRED(_, APP(CONST(_), args), _) -> begin match args with
    | CONST(s) :: t -> s
    | APP(CONST(s), _) :: t -> s
    | _ -> "noname"
    (* TODO FIXME commented out because this method is sometimes called for structural rules *)
    (*failwith "Error while getting the name of a connective. Are you sure this is an introduction rule specification?"*)
    end
  | _ -> failwith ("Error getting the name of a connective: " ^ (Prints.termToString (getHeadPredicate f)))
;;

let getObjectLogicMainFormula f = match getHeadPredicate f with
  | PRED(_, APP(CONST(_), h::tl), _) -> h
  | _ -> failwith ("Error getting the object logic's main formula from a specification: " ^ (Prints.termToString (getHeadPredicate f)))
;;

let getRuleName f = (getConnectiveName f) ^ "_" ^ (getSide f) ;; 


(* Checks if a formula is a bipole *)
(* 
  Grammar for bipoles and monopoles:
  B = not A | M | !M | B + B | B * B | exists B
  M = A | ?A | M & M | M \par M | forall M
*)
let rec isMonopole f = match f with
  | PRED(_,_,_) | EQU(_,_,_) -> true
  | ZERO | TOP -> true
  | WITH(m1, m2) -> isMonopole m1 && isMonopole m2
  | PARR(m1, m2) -> isMonopole m1 && isMonopole m2
  | FORALL(_,_, m) -> isMonopole m
  (* Questions marks may have only atomic scope *)
  | QST(_, PRED(_,_,_)) -> true
  | _ -> false

let rec isBipole f = match f with
  | m when isMonopole m -> true
  | NOT(PRED(_,_,_)) -> true
  | ONE | BOT -> true
  | TENSOR(b1, b2) -> isBipole b1 && isBipole b2
  | ADDOR(b1, b2) -> isBipole b1 && isBipole b2
  | EXISTS(_,_, b) -> isBipole b
  | ABS(_,_, b) -> isBipole b
  (* Bangs can only be applied to monopoles *)
  | BANG(_, m) -> isMonopole m
  | _ -> false

(* Transforms a formula to negated normal form *)
let rec nnf f = match f with
  | PRED(str, terms, p) -> f 
  | TENSOR(f1, f2) -> TENSOR(nnf f1, nnf f2)
  | PARR(f1, f2) -> PARR(nnf f1, nnf f2)
  | WITH(f1, f2) -> WITH(nnf f1, nnf f2)
  | ADDOR(f1, f2) -> ADDOR(nnf f1, nnf f2)
  | EXISTS(s, i, f1) -> EXISTS(s, i, nnf f1)
  | FORALL(s, i, f1) -> FORALL(s, i, nnf f1)
  | QST(s, f1) -> QST(s, nnf f1)
  | BANG(s, f1) -> BANG(s, nnf f1)
  (* TODO: check this lolli transformation *)
  | LOLLI(s, f1, f2) -> PARR(nnf (NOT(QST(s, f1))), nnf f2)
  | ABS(s, i, f1) -> ABS(s, i, nnf f1)
  | TOP -> TOP
  | ZERO -> ZERO
  | BOT -> BOT
  | ONE -> ONE
  | NOT(t) -> begin
    match t with
      | NOT(t1) -> t1
      | PRED(str, terms, p) -> NOT(t) 
      | TENSOR(f1, f2) -> PARR(nnf (NOT(f1)), nnf (NOT(f2)))
      | PARR(f1, f2) -> TENSOR(nnf (NOT(f1)), nnf (NOT(f2)))
      | WITH(f1, f2) -> ADDOR(nnf (NOT(f1)), nnf (NOT(f2)))
      | ADDOR(f1, f2) -> WITH(nnf (NOT(f1)), nnf (NOT(f2)))
      | EXISTS(s, i, f1) -> FORALL(s, i, nnf (NOT(f1)))
      | FORALL(s, i, f1) -> EXISTS(s, i, nnf (NOT(f1)))
      | QST(s, f1) -> BANG(s, nnf (NOT(f1)))
      | BANG(s, f1) -> QST(s, nnf (NOT(f1)))
      | LOLLI(s, f1, f2) -> TENSOR(nnf (QST(s, f2)), nnf (NOT(f1)))
      | ABS(s, i, f1) -> ABS(s, i, nnf (NOT(f1)))
      | TOP -> ZERO
      | ZERO -> TOP
      | BOT -> ONE
      | ONE -> BOT
      | COMP(ct, t1, t2) -> begin
        match ct with
          | EQ -> COMP(NEQ, t1, t2)
          | NEQ -> COMP(EQ, t1, t2)
          | LESS -> COMP(GEQ, t1, t2)
          | GEQ -> COMP(LESS, t1, t2)
          | GRT -> COMP(LEQ, t1, t2)
          | LEQ -> COMP(GRT, t1, t2)
        end
      | _ -> failwith "Error while transforming to negated normal form."
    end
  | _ -> failwith "Error while transforming to negated normal form."
 
(* Solves an arithmetic expression *)
let rec solve_exp e = match e with
  | INT (x) -> x
  | VAR v -> 1(* Infer the variable value?? *)
  | PLUS (x, y) -> (solve_exp x) + (solve_exp y)
  | MINUS (x, y) -> (solve_exp x) - (solve_exp y)
  | TIMES (x, y) -> (solve_exp x) * (solve_exp y)
  | DIV (x, y) -> (solve_exp x) / (solve_exp y)
  | PTR {contents = T t} -> solve_exp t
  | PTR {contents = V t} when t.tag = LOG -> 
      failwith "ERROR: Cannot handle comparisons with logical variables."
  | bla -> failwith "ERROR: Unexpected term in a comparison."
;;

(* Solves an arithmetic comparison *)
let solve_cmp c e1 e2 = 
  let n1 = solve_exp e1 in 
  let n2 = solve_exp e2 in
    match c with
      | EQ -> n1 = n2
      | LESS -> n1 < n2
      | GEQ -> n1 >= n2        
      | GRT -> n1 > n2
      | LEQ -> n1 <= n2
      | NEQ -> n1 != n2
;;

let fVarC x = match x with
| "$test" -> 10
| _ -> 0;;

let varName x y = "$"^x^(string_of_int y);;

let rec tCheckAuxList term = TINT

let rec deref t = match t with
  | PTR {contents = T t1} -> deref t1
  | t -> t
;;

(* Transforms abstractions into universal quantifiers *)
let rec abs2forall f = match f with
  | ABS(s, i, t) -> FORALL(s, i, abs2forall t)
  | t -> t
;;

(* Transforms abstractions into existential quantifiers *)
let rec abs2exists f = match f with
  | ABS(s, i, t) -> EXISTS(s, i, abs2exists t)
  | t -> t
;;

(* Binding variables *)

(* Binding a variable to a term. The *contents* of the cell representing the
 * variable is a reference which must be updated. Also the variable must
 * not be made a reference to itself. This can be changed to mimic the
 * Prolog representation of bound variables but then deref will have to
 * work differently. This is the place to introduce trailing. *)

type state = int
let bind_stack = Stack.create ()
let bind_len = ref 0

let save_state () = !bind_len

let restore_state n =
  assert (n <= !bind_len) ;
  for i = 1 to !bind_len-n do
    let (v,contents) = Stack.pop bind_stack in
    v := contents
  done ;
  bind_len := n

type subst = (ptr*in_ptr) list
type unsubst = subst

let bind v t =
  let dv = match deref v with
    | PTR t -> t
    | _ -> assert false (* [v] should represent a variable *)
  in
  let dt = deref t in
  if match dt with PTR r when r==dv -> false | _ -> true then begin
    Stack.push (dv,!dv) bind_stack ;
    dv := T dt ;
    incr bind_len
  end

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

(* Extracts the string from a CONST *)
let extract_str c = match c with
  | CONST(str) -> str
  | _ -> failwith "Trying to extract the string for the worng term or this case is not implemented."

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
    (*| VAR _, _ | _, VAR _ -> assert false*)
    | VAR {tag=EIG; id=i1}, VAR {tag=EIG; id=i2} when i1 = i2 -> true
    | VAR _, _ | _, VAR _ -> false
    | SUSP (t,ol,nl,e), SUSP (tt,oll,nll,ee) ->
        ol = oll && nl = nll && eq t tt &&
          List.fold_left2
            (fun test e1 e2 ->
               test && match e1,e2 with
                 | Dum i, Dum j when i = j -> true
                 | Binding (t,i), Binding (tt,j) when i=j && eq t tt -> true
                 | _ -> false)
            true e ee
    (*| CONST s1, CONST s2 -> s1 = s2*)
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
      match deref t with
        | ABS (_,n',t') -> aux (n+n') t'
        | _ -> ABS ("*",n,t)
    in
    aux n t


let susp t ol nl e = SUSP (t,ol,nl,e)

let app a b = if b = [] then a else match observe a with
  | APP(a,c) -> APP (a,c @ b)
  | _ -> APP (a,b)

let db n = DB n

let rec remove_abs clause = 
  match clause with
    | ABS (str, i, t) -> remove_abs t
    | _ -> clause

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
    | CONST (t1) -> CONST (t1)
    (*| LIST (t1) -> LIST(t1)*)
    (*| NB i*) | DB i as x -> x
    | SUSP _ | PTR _ -> assert false
    | t -> failwith "Unexpected case. (term.ml copy_eigen)"
  in
    cp tm

(** {1 Convenience} *)

(*
let string text = get_var_by_name ~tag:CONST ~lts:0 ~ts:0 text
*)

(*
let binop s a b = APP ((atom s),[a;b])
*)

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

(**/**) 
