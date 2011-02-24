(* Data structures used during proof search *)

open Term

(* Verbose on/off *)
let verbose = ref false ;;

(* Integer to indicate how many tensors I am solving, so that I only check for context emptyness at the end *)
let tensor = ref 0 ;;

(* Number of states saved *)
let nstates = ref 0 ;;

(* List to hold the main formulas (everything is here initially *)
let (goals : (terms list) ref) = ref [] ;;

(* List to hold positive formulas *)
let (positives : (terms list) ref) = ref [] ;;

(* List to hold the atoms *)
let (atoms : (terms list) ref) = ref [] ;;

(*let (bck_cls : (terms list) ref) = ref [] ;;*)
let is_top = ref (false);;

(* Hashtable for the context (subexponential indexes are the keys, list of formulas is the entry) *)
let (context : ((string, terms list) Hashtbl.t) ref ) = ref (Hashtbl.create 100) ;;
Hashtbl.add !context "$gamma" [] ;;

(* Hashtable for clauses 
 * A clause A :-[s] B is stored as: 
 * A should be a PRED (str, terms)
 * str ---> [ (LOLLI(s, A, B)) ]
 *)
let (clausesTbl : ( ( (string, terms list) Hashtbl.t) ref)) = ref (Hashtbl.create 100) ;;

(* Hashtable with subexponentials' types ($gamma is the linear context and
 * $def holds the definitions (definitions are not being used yet)) 
 *)
let subexTpTbl = Hashtbl.create 100 ;;
Hashtbl.add subexTpTbl "$gamma" (LIN) ;;
Hashtbl.add subexTpTbl "$def" (UNB) ;;

(* Hashtable with subexponentials' parcial order *)
(* Each subexponential holds those which are greater than it. *)
let (subexOrdTbl : (string, string) Hashtbl.t ) = Hashtbl.create 100 ;;

type phase = 
| ASYN
| SYNC
;;

let print_phase p = match p with
  | ASYN -> print_string "asyn"
  | SYNC -> print_string "sync"
;;

(* goals, positives, atoms, context, clauses table *)
type data = 
| DATA of (terms list) * (terms list) * (terms list) * 
          ((string, (terms list)) Hashtbl.t) * 
          ((string, terms list) Hashtbl.t) * bool
;;

(* State:
 * data: tables and etc.
 * terms: formula chosen
 * int: bind_len
 * (unit -> unit): success function
 * (unit -> unit): failure function
 * terms list: list of possible bodies for an atom
 * phase: synchronous or asynchronous
 *)
type state = 
| STATE of data * terms * int * (unit -> unit) * (unit -> unit) * (terms list) * phase ;;

let print_state s = match s with
  | STATE(dt, form, br, fun1, fun2, l, p) -> print_string "State: "; print_term form; print_newline ()
;;

let print_stack s = print_string "STACK\n"; Stack.iter (print_state) s; print_string "EndOfSTACK\n" ;;

(* Stack to save the sequents on non-deterministic choices *)
let (states : (state Stack.t) ref) = ref (Stack.create ()) ;;

(*
(* Example of subexponentials *)
Hashtbl.add subexTpTbl "$i" (LIN);;
Hashtbl.add subexTpTbl "$j" (AFF);;
Hashtbl.add subexTpTbl "$k" (REL);;
Hashtbl.add subexTpTbl "$l" (UNB);;
(* Example of subexponentials ordering: i < j < k *)
Hashtbl.add subexOrdTbl "$i" "$j";;
Hashtbl.add subexOrdTbl "$i" "$k";;
Hashtbl.add subexOrdTbl "$j" "$k";;
(* Putting some formulas on the context - empty list indicates an empty subexponential *)
Hashtbl.add !context "$i" ((WITH (TOP, TOP) )::[]);;
Hashtbl.add !context "$gamma" [] ;;
Hashtbl.add !context "$j" [] ;;
Hashtbl.add !context "$k" [] ;;
Hashtbl.add !context "$l" [] ;;
*)

(* Returns the type of a subexponential *)
let type_of s = try 
  Hashtbl.find subexTpTbl s
  with Not_found -> failwith ("[ERROR] Subexponential "^s^" has no type defined.")
;;

let rec get_pred form = match form with
  | ABS(s, i, t) -> get_pred t
  | LOLLI(s, head, body) -> (match head with
    | PRED(str, t) -> str
    | _ -> failwith "Head of a lolli is not a predicate."
    )
  | _ -> failwith "No lolli inside abstraction."
;;

(* Removes an element from a list *)
(* Important note: removes only the first occurence of the element *)
let rec remove elm lst = 
  match lst with
    | [] -> []
    | e::t when e = elm -> t
    | h::t -> h :: (remove elm t)
;;

let make_first elm lst = elm :: (remove elm lst) ;;

(* Decides if an element e is in a list l *)
let rec in_list l e = try match List.hd l with
    | h when h = e -> true
    | _ -> in_list (List.tl l) e
    with Failure "hd" -> false
;;

(* Inserts a formula in a subexponential *)
let add_ctx f s = try match Hashtbl.find !context s with
  | forms -> 
    Hashtbl.remove !context s; 
    Hashtbl.add !context s (f :: forms)
  with Not_found ->
    Hashtbl.add !context s (f :: [])
;;

(* Inserts a clause in the clauses hashtable *)
let add_cls clause = 
  let predname = get_pred clause in
  try match Hashtbl.find !clausesTbl predname with
  | clauseslst ->
    Hashtbl.remove !clausesTbl predname; 
    Hashtbl.add !clausesTbl predname (clause :: clauseslst) 
  with Not_found ->    
    Hashtbl.add !clausesTbl predname (clause :: []) 
;;

let bind_stack = Stack.create () ;;
let bind_len = ref 0 ;;

let save_state () = !bind_len ;;

let restore_state n =
  assert (n <= !bind_len) ;
  for i = 1 to !bind_len-n do
    let (v,contents) = Stack.pop bind_stack in
      v := contents;
  done ;
  bind_len := n
;;

type subst = (ptr*in_ptr) list
type unsubst = subst

let rec deref t = match t with
  | PTR {contents = T t1} -> deref t1
  | t -> t
;;

let bind v t = 
  let dv = match deref v with
    | PTR t ->  t (* t is supposed to be a variable here *)
    | _ -> assert false (* [v] should represent a variable *)
  in
  let dt = deref t in (* r is a variable equal to dv (binding X to X makes no sense) *)
    if match dt with PTR r when r == dv -> false | _ -> true then begin
      Stack.push (dv,!dv) bind_stack ;
      dv := T dt ;
      incr bind_len 
    end
;;

let last_fail () = match Stack.top !states with
  | STATE(_, _, _, _, f, _, _) -> f ()
;;

(* Removes a formula from a subexponential (only the first occurence) *)
let rmv_ctx form subexp = 
  let forms = Hashtbl.find !context subexp in
  let new_list = remove form forms in
    Hashtbl.remove !context subexp; Hashtbl.add !context subexp new_list
;;

(* Removes a clause from the hashtable *)
let rmv_cls clause = match (Term.remove_abs clause) with
  | LOLLI (s, f1, f2) -> (match f1 with
    | PRED (str, terms) -> (
      try match Hashtbl.find !clausesTbl str with
        | clauseslst ->
          let newclauses = remove clause clauseslst in
            Hashtbl.remove !clausesTbl str; Hashtbl.add !clausesTbl str newclauses
        with Not_found -> failwith "Trying to remove a clause from a non-existing predicate."
    )
    | _ -> failwith "Body of a clause not a predicate."
  )
  | _ -> print_term clause; failwith "Clause is not an implication."
;;

(* Inserting a formula in Gamma (linear context) *)
let add_lin form = add_ctx form "$gamma" ;;

(* Inserts a formula in the main formulas' list *)
let add_goals form = goals := form :: !goals ;;

(* Inserts a formula in the positive formulas' list *)
let add_pos form = positives := form :: !positives ;;

(* Inserts a formula in the atoms' list *)
let add_atm a = atoms := a :: !atoms ;;

(* Get all the keys from a hash table, including duplicates *)
let keys ht = Hashtbl.fold (fun key data accu -> key :: accu) ht [] ;;

let print_hashtbl h = print_string "\nHashTable:\n";
  let keylst = keys h in
  let rec print_h lst = 
    match lst with
      | [] -> print_string "\nendOfTable\n\n"
      | k :: t -> print_string ("["^k^"] "); print_list_terms (Hashtbl.find h k); print_newline (); print_h t
  in print_h keylst
;;

let clear_tables () = 
  Hashtbl.clear !context; 
  Hashtbl.clear !clausesTbl; 
  Hashtbl.clear subexTpTbl; 
  Hashtbl.clear subexOrdTbl;
  Hashtbl.clear tTbl;
  Hashtbl.clear kTbl;
  Hashtbl.clear rTbl;
  Hashtbl.add kTbl "o" (TPRED); 
  Hashtbl.add !context "$gamma" [];
  Hashtbl.add subexTpTbl "$gamma" (LIN);
  Hashtbl.add subexTpTbl "$def" (UNB)
;;
