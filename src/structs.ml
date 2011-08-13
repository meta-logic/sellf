(* Data structures used during proof search *)

open Term

(* Verbose on/off *)
let verbose = ref false ;;
let tabling = ref false ;;

(* Timer on/off *)
let time = ref false ;;

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
let rec remove_element a lst acc = 
  match lst with 
  | [] -> acc
  | a1 :: t when a1 = a -> acc @ t
  | b :: t -> remove_element a t (acc @ [b])
(* Important note: removes only the first occurence of the element *)
let rec remove elm lst = remove_element elm lst []
  (*match lst with
    | [] -> []
    | e::t when e = elm -> t
    | h::t -> h :: (remove elm t)*)
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
  Hashtbl.clear kTbl;
  Hashtbl.clear tTbl;
  Hashtbl.clear rTbl;
  Stack.clear !states;
  Stack.clear bind_stack;
  goals := [];
  positives := [];
  atoms := [];
  bind_len := 0;
  nstates := 0;
  Hashtbl.add kTbl "o" (TPRED);  
  Hashtbl.add !context "$gamma" [];
  Hashtbl.add subexTpTbl "$gamma" (LIN)
;;

let init_context  : ((string, terms list) Hashtbl.t) ref = ref (Hashtbl.create 100) ;; 
let init_clausesTbl  : ( ( (string, terms list) Hashtbl.t) ref) = ref (Hashtbl.create 100) ;;

let saveInitState () = 
  init_context := Hashtbl.copy !context;
  init_clausesTbl := Hashtbl.copy !clausesTbl
;;

let recoverInitState () = 
  Stack.clear !states;
  Stack.clear bind_stack;
  (* G: the facts consumed should not return to the contexts. 
  Watch out. Even if you uncomment this, it does not have the expected result
  since the copy method does not make copies of the data structure stored inside
  the hash.*)
(*  context := !init_context;
  clausesTbl := !init_clausesTbl;*)
  goals := [];
  positives := [];
  atoms := [];
  bind_len := 0;
  nstates := 0
;;

let remove_states n = let s = Stack.length !states in
  if !verbose then begin
    print_string "Removing states: "; 
    print_int n; print_newline ()
  end;
  assert (n <= s);
  for i = 1 to s-n do
    let STATE(_, _, _, _, _, _, _) = Stack.pop !states in
      nstates := !nstates - 1
  done;
;;

(*----------------------------------------------------------
Code for implementing tabled deduction.
-----------------------------------------------------------*)

let (fail_table : ((Term.terms, (string, terms list) Hashtbl.t) Hashtbl.t) ref ) = ref (Hashtbl.create 100) ;;

(*Removes a term from a list of terms.*)
let rec remove_element_terms a lst acc = 
  match lst with 
  | [] -> acc
  | a1 :: t when Term.observe a1 = Term.observe a -> acc @ t
  | b :: t -> remove_element_terms a t (acc @ [b])

let rec member_term_lst h lst = 
  match lst with
  | [] -> false
  | h1 :: t when Term.observe h = Term.observe h1 -> true
  | h1 :: t -> member_term_lst h t

let rec equiv_lst_terms lst1 lst2 = 
 match lst1 with
 | [] -> if lst2 = [] then true else false
 | h :: t -> if member_term_lst h lst2 then
                  equiv_lst_terms t (remove_element_terms h lst2 [])
                else false
    
(*Checks whether all the lists associated to the keys in keylst are empty*)
let rec all_empty keylst tbl = 
  match keylst with
  | [] -> true
  | h :: t -> if Hashtbl.find tbl h = [] 
                then all_empty t tbl else false

(*Checks whether there is an equivalent new subexponential that contains the 
same formulas as in lst*)
let rec find_equiv_new_context lst keys tbl =
  match keys with
  | [] -> failwith "NO_KEY"
  (*We add the 0000000 to h to avoid a Substring failure.*)
  | h :: t when String.sub (h^"00000000") 0 7 = "NSUBEXP" -> 
                if equiv_lst_terms lst (Hashtbl.find tbl h) 
                then h else find_equiv_new_context lst t tbl
  | h :: t -> find_equiv_new_context lst t tbl

(*Checks whether the context of two sequents are the same, that is, their 
associated hashtbls are the same.*)
let rec equiv_sequents tbl1 tbl2 = 
  let rec equiv_aux keylst1 keylst2 tbl1 tbl2 =
    match keylst1 with
    | [] -> if all_empty keylst2 tbl2  then true else false
    | h :: t -> 
              (*We add the 0000000 to h to avoid a Substring failure.*)
              if String.sub (h^"0000000") 0 7 = "NSUBEXP" then (*This is the case when the subexponential is new*)
              begin
              try 
                let h1 = find_equiv_new_context (Hashtbl.find tbl1 h) keylst2 tbl2 in
                let key_aux = remove_element h1 keylst2 [] in
                equiv_aux t key_aux tbl1 tbl2 
              with (*We capture the case when there is no new subexponential with the same context by using 
                      a failure.*)
                | Failure "NO_KEY" -> false 
              end
              else if List.mem h keylst2 && equiv_lst_terms (Hashtbl.find tbl1 h) (Hashtbl.find tbl2 h) 
              then 
                  let key_aux = remove_element h keylst2 [] in 
                  equiv_aux t key_aux tbl1 tbl2 
               else false
in 
let keylst1 = keys tbl1 in 
let keylst2 = keys tbl2 in 
  equiv_aux keylst1 keylst2 tbl1 tbl2


(*Checks all contexts associated to a goal formula whether there is an equivalent one.*)
let rec not_in_fail_table h = 
  let rec not_in_fail_table_aux lst = 
  match lst with
  | [] -> true
  | tbl1 :: t -> if equiv_sequents !context tbl1 then
                     false else not_in_fail_table_aux t
in 
let hashlst = Hashtbl.find_all !fail_table h
in 
not_in_fail_table_aux hashlst
                      
