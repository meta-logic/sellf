(* Data structures used during proof search *)

open Term
open Prints

(* Verbose on/off *)
let verbose = ref false ;;
(* Tabling on/off *)
let tabling = ref false ;;
(* Timer on/off *)
let time = ref false ;;

(* Integer to indicate how many tensors I am solving, 
 * so that I only check for context emptyness at the end *)
let tensor = ref 0 ;;

let is_top = ref (false);;

type phase = 
| ASYN
| SYNC
;;

let print_phase p = match p with
  | ASYN -> print_string "asyn"
  | SYNC -> print_string "sync"
;;

(******************* LISTS ************************)
(*
 * Auxiliary functions for lists.
 *)

(* Removes an element from a list *)
let rec remove_element a lst acc = 
  match lst with 
  | [] -> acc
  | a1 :: t when a1 = a -> acc @ t
  | b :: t -> remove_element a t (acc @ [b])
(* Important note: removes only the first occurence of the element *)
let rec remove elm lst = remove_element elm lst []
;;

(* Remove the elements of rem from the list lst *)
let rec removeLst rem lst = match rem with
  | [] -> lst
  | hd::tl -> removeLst tl (remove hd lst)

let make_first elm lst = elm :: (remove elm lst) ;;

(* Decides if an element e is in a list l *)
let rec in_list l e = try match List.hd l with
    | h when h = e -> true
    | _ -> in_list (List.tl l) e
    with Failure "hd" -> false
;;

(******************* HASHTABLES ************************)
(*
 * Auxiliary functions for hashtables.
 *)

(* Get all the keys from a hash table, including duplicates *)
let keys ht = Hashtbl.fold (fun key data accu -> key :: accu) ht [] ;;

(* Transforms a hashtable into a list of pairs *)
(* Note that the hashtable data is a list. *)
let to_pairs ht = Hashtbl.fold (fun key data acc -> 
  let rec pairs k lst = match lst with
    | [] -> []
    | elm :: tl -> (k, elm) :: pairs k tl
  in
  (pairs key data) @ acc
  ) ht [] ;;

let print_hashtbl h = print_string "\nHashTable:\n";
  let keylst = keys h in
  let rec print_h lst = 
    match lst with
      | [] -> print_string "\n"
      | k :: t -> 
        print_string ("["^k^"] "); 
        print_list_terms (Hashtbl.find h k); 
        print_newline (); print_h t
  in print_h keylst
;;

(******************* ATOMS ************************)
(*
 * Functions to handle atoms' polaritites.
 *)

(* Hashtable to store the polarities *)
let atomspol : (string, polarity) Hashtbl.t ref = ref (Hashtbl.create 100) ;; 

let addAtomPol s p = 
  try match Hashtbl.find !atomspol s with
    | _ -> failwith ("[ERROR] Polarity of "^s^" already declared.") 
    with Not_found -> Hashtbl.add !atomspol s p 
;;

let getAtomPol s = 
  try match Hashtbl.find !atomspol s with
    | p -> p
    with Not_found -> 
      (*print_string ("[WARNING] Atom "^s^" has no polarity defined, considering it negative.\n");*)
      NEG
;;

(***************** SUBEXPONENTIALS ***************)

(* Hashtable with subexponentials' types ($gamma is the linear context and
 * $def holds the definitions (definitions are not being used yet)) 
 *)
let subexTpTbl = Hashtbl.create 100 ;;
(*Hashtbl.add subexTpTbl "$gamma" (LIN) ;;
Hashtbl.add subexTpTbl "$def" (UNB) ;;*)

(* Hashtable with subexponentials' parcial order *)
(* Each subexponential holds those which are greater than it. *)
let (subexOrdTbl : (string, string) Hashtbl.t ) = Hashtbl.create 100 ;;

(* Returns the type of a subexponential *)
let type_of s = try 
  Hashtbl.find subexTpTbl s
  with Not_found -> failwith ("[ERROR] Subexponential "^s^" has no type defined.")
;;

(* Gets all the unbounded subexponentials and make them greater then s 
 * (put in s' order list) *)
let lt_unbounded s = let subexps = keys subexTpTbl in
  let rec get_unbounded lst = match lst with
    | [] -> ()
    | u :: t -> (match Hashtbl.find subexTpTbl s with
      | UNB -> Hashtbl.add subexOrdTbl s u; (get_unbounded t)
      | _ -> get_unbounded t
    )
  in get_unbounded subexps
;;

(* Checks if a subexponential s1 > s2 *)
let rec bfs root queue goal = match queue with
  | [] -> false
  | h :: t when h = root -> failwith "Circular dependency on subexponential order."
  | h :: t when h = goal -> true
  | h :: t -> bfs root (t @ Hashtbl.find_all subexOrdTbl h) goal
;;
let greater_than s1 s2 = bfs s2 (Hashtbl.find_all subexOrdTbl s2) s1 ;;

(* Returns a list with all subexponentials from idxs that will have their 
 * formulas erased if !s is applied. *)
let rec erased s idxs = match idxs with
  | [] -> []
  | i::t -> 
    match type_of i with
      | UNB | AFF -> 
        if i = "$infty" || i = s || (greater_than i s) then erased s t
        else i::(erased s t)
      | _ -> erased s t
;;
let erased_bang s = erased s (keys subexTpTbl) ;;
(* Returns a list with all subexponentials from idxs that will be checked 
 * for emptiness if !s is applied. *)
let rec checked_empty s idxs = match idxs with
  | [] -> []
  | i::t -> 
    match type_of i with
      | REL | LIN -> 
        if i = "$gamma" || i = s || (greater_than i s) then checked_empty s t
        else i::(checked_empty s t)
      | _ -> checked_empty s t
;;
let empty_bang s = checked_empty s (keys subexTpTbl) ;;

(* Checks whether or not a subexponential can suffer weakening *)
let weak i = match type_of i with
  | UNB | AFF -> true
  | REL | LIN -> false
;;

(******************* FOCUSED ************************)
(*
 * The focused part of the sequent can be a formula or a list of them.
 * The order in which these formulas should be solved is negatives, positives,
 * atoms. This is why I divided this list in three: initially everything in in
 * 'goals'. When positive formulas are found, they are put in 'positives' and
 * when atoms are found they are put in 'atoms'.
 *
 * G - Note to self: a decide rule consists in choosing a clause to focus on 
 * such that the head matches the atom that we are trying to prove. This is
 * valid because there's a constraint that the head of a lolli is always an
 * atom or a lolli itself (in which case it will be decomposed before inserting
 * in the context).
 * In order to prove coherence, this restriction makes things harder, so we
 * should do a blind proof search, that can choose arbitrary formulas from the
 * context and without the lolli restriction on the syntax. Also, we should do
 * a bounded proof search.
 *)

(* List to hold the main formulas (everything is here initially *)
let (goals : (terms list) ref) = ref [] ;;
(* Inserts a formula in the main formulas' list *)
let add_goals form = goals := form :: !goals ;;
(* TODO: I think the function above is not used very often. Consider
 * changing this to an update goals which will remove the head and add a new formula. *)

(* List to hold positive formulas *)
let (positives : (terms list) ref) = ref [] ;;
(* Inserts a formula in the positive formulas' list *)
let add_pos form = positives := form :: !positives ;;

(* List to hold the atoms *)
let (atoms : (terms list) ref) = ref [] ;;
(* Inserts a formula in the atoms' list *)
let add_atm a = atoms := a :: !atoms ;;

(******************** CONTEXT **********************)
(*
 * A hashtable implements the context of a sequent. The key is the
 * name of the subexponential, and this is mapped to a list of formulas.
 * The linear formulas (not marked with ?l) are stored with the key '$gamma'.
 * The list of '$gamma' is initalized by hand. All the other subexponentials are
 * created in the table when there's the need to insert a formula in them.
 *)

(* Hashtable for the context *)
let (context : ((string, terms list) Hashtbl.t) ref ) = ref (Hashtbl.create 100) ;;
(*Hashtbl.add !context "$gamma" [] ;;*)

let init_context  : ((string, terms list) Hashtbl.t) ref = ref (Hashtbl.create 100) ;; 

(* Inserts a formula in a subexponential *)
let add_ctx f s = try match Hashtbl.find !context s with
  | forms -> 
    Hashtbl.remove !context s; 
    Hashtbl.add !context s (f :: forms)
  with Not_found -> failwith ("Trying to add a formula to "^s^" but it was not
  declared.\n")
    (*Hashtbl.add !context s (f :: [])*)
;;

(* Inserts a formula in Gamma (linear context) *)
let add_lin form = add_ctx form "$gamma" ;;

(* Removes a formula from a subexponential (only the first occurence) *)
let rmv_ctx form subexp = 
  let forms = Hashtbl.find !context subexp in
  let new_list = remove form forms in
    Hashtbl.remove !context subexp; Hashtbl.add !context subexp new_list
;;

(* Returns all the formulas in the subexponential s or an empty list if it's
 * empty *)
let get_forms s = try match Hashtbl.find !context s with
  | x -> x
  with Not_found -> failwith ("Trying to get the formulas from "^s^" but it was
  not declared.")
    (*[]*)

(* Checks whether a formula f is in subexponential s *)
let in_subexp f s = in_list f (get_forms s) ;;

(* Returns a list with all the formulas that cannot suffer weakening *)
let not_weakenable () = Hashtbl.fold (fun s forms l -> 
    if not (weak s) then 
    begin
      forms@l
    end
    else l) !context [] ;;

(* Checks whether K context is empty on the subexponentials that cannot suffer weakening *)
(* TODO: fix the TOP thing. *)
let empty_nw () =
  match (List.length (not_weakenable ())) with
    | 0 -> if !verbose then print_string "Non-weakenable set is empty"; true
    | n -> if !is_top then begin
        if !verbose then (print_string "However, the proof has a top.\n");
        true
      end
      else false
;;

(* Checks if bang rule can be applied with subexponential s *)
let condition_bang s = 
  let subsempt = empty_bang s in
  let rec all_empty subs = match subs with
    | [] -> true
    | h::t -> match get_forms h with
      | [] -> all_empty t
      | _ -> 
        if !verbose then 
          print_string ("Failed in bang rule with subexponential: "^s^"\n"); 
	      false
  in all_empty subsempt
;;

(* Removes all formulas from a subexponential *)
let remove_all s = Hashtbl.remove !context s; Hashtbl.add !context s [] ;;

(* Operation k <l for K context *)
(* NOTE: $infty is greater than everybody, no need to put this in the hash. *)
let k_less_than s = Hashtbl.iter (fun idx forms -> 
  if not (idx = "$gamma") && not (idx = "$infty") && not (idx = s) && not (greater_than idx s) then begin 
    if !verbose then print_string ("Removing from "^idx^" in k_less_than "^s^"\n"); 
    remove_all idx 
  end) 
  !context;;

(* Verifies if a subexponential is empty *)
let empty s = List.length (Hashtbl.find !context s) == 0 ;;

(* Creating a new subexponential *)
let new_subexp s = 
  try match Hashtbl.find subexTpTbl s with
  | _ -> ()
  with Not_found -> 
    Hashtbl.add subexTpTbl s (AFF); 
    Hashtbl.add !context s []; 
    lt_unbounded s ;;

(******************** CLAUSES **********************)
(* 
 * Hashtable for clauses 
 * A clause A :-[s] B is stored as: 
 * A should be a PRED (str, terms)
 * str ---> [ (LOLLI(s, A, B)) ]
 *
 * This is useful when backchaining, so we can find the right clauses to focus
 * on quickly. Note that this is only valid if the head of the clause is
 * atomic. So it is not used on the blind proof search.
 *)

(* Hashtable *)
let (clausesTbl : ( ( (string, terms list) Hashtbl.t) ref)) = ref (Hashtbl.create 100) ;;

let init_clausesTbl  : ( ( (string, terms list) Hashtbl.t) ref) = ref (Hashtbl.create 100) ;;

(* Returns the predicate that is the head of form 
 * (in the case form is a lolli with atomic head) *)
let rec get_pred form = match form with
  | ABS(s, i, t) -> get_pred t
  | LOLLI(s, head, body) -> (match head with
    | PRED(str, t, _) -> str
    | _ -> failwith "Head of a lolli is not a predicate."
    )
  | _ -> failwith "No lolli inside abstraction."
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

(* Removes a clause from the hashtable *)
let rmv_cls clause = match (Term.remove_abs clause) with
  | LOLLI (s, f1, f2) -> (match f1 with
    | PRED (str, terms, _) -> (
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

(***************** BACKTRACKING **********************)
(*
 * Gathered here are everything related with the storing of states used during
 * backchaining.
 *)

(* Datatype used to store:
 * goals, positives, atoms, context, clauses table 
 * respectively.
*)
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

(* Number of states saved *)
let nstates = ref 0 ;;

(* Stack to save the sequents on non-deterministic choices *)
let (states : (state Stack.t) ref) = ref (Stack.create ()) ;;
let bind_stack = Stack.create () ;;
let bind_len = ref 0 ;;

let saveInitState () = 
  init_context := Hashtbl.copy !context;
  init_clausesTbl := Hashtbl.copy !clausesTbl;
;;

let recoverInitState () = 
  Stack.clear !states;
  Stack.clear bind_stack;
  (* G: the facts consumed should not return to the contexts. 
  Watch out. Even if you uncomment this, it does not have the expected result
  since the copy method does not make copies of the data structure stored inside
  the hash.*)
(*  context := !init_context;*)
(*  clausesTbl := !init_clausesTbl;*)
(*  print_endline "Recovered context:";
  print_hashtbl !context;
  print_endline "Recovered clauses:";
  print_hashtbl !clausesTbl;*)
  goals := [];
  positives := [];
  atoms := [];
  bind_len := 0;
  nstates := 0
;;

(* Saves the state for backtracking later (called whenever a non-deterministic
 * choice is made, i.e., when a positive formula or atom is focused on) *)
let save_state form bind suc fail bck_clauses phs =  
  let ctx_cp = Hashtbl.copy !context in
  let cls_cp = Hashtbl.copy !clausesTbl in
  let dt = DATA(!goals, !positives, !atoms, ctx_cp, cls_cp, !is_top) in
  let st = STATE(dt, form, bind, suc, fail, bck_clauses, phs) in
  nstates := !nstates + 1;
  if !verbose then begin
    print_string "+++++ Saving formula "; 
    print_term form; print_string " on state stack in phase ";
    print_phase phs; print_newline ();
  end;
  Stack.push st !states;
;;

(* Recovers the information inside dt *)
let reset dt = match dt with
  | DATA (g, p, a, c, ct, isT) ->
    goals := g;
    positives := p;
    atoms := a;
    context := Hashtbl.copy c;
    clausesTbl := Hashtbl.copy ct;
    is_top := isT
;;

let restore_state n =
  assert (n <= !bind_len) ;
  for i = 1 to !bind_len-n do
    let (v,contents) = Stack.pop bind_stack in
      v := contents;
  done ;
  bind_len := n
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

let print_state s = match s with
| STATE(dt, form, br, fun1, fun2, l, p) -> print_string "State: "; print_term form; print_newline ()
;;

let print_stack s = print_string "STACK\n"; Stack.iter (print_state) s; print_string "EndOfSTACK\n" ;;

let last_fail () = match Stack.top !states with
  | STATE(_, _, _, _, f, _, _) -> f ()
;;

(******************* POINTERS ******************)
(*
 * Functions related to pointers
 *)

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

(************************ EXTRAS **********************)

let initialize () = 
  Hashtbl.clear !context; 
  Hashtbl.clear !clausesTbl; 
  Hashtbl.clear subexTpTbl; 
  Hashtbl.clear subexOrdTbl; 
  Hashtbl.clear kindTbl;
  Hashtbl.clear typeTbl;
  (*Hashtbl.clear rTbl;*)
  Stack.clear !states;
  Stack.clear bind_stack;
  goals := [];
  positives := [];
  atoms := [];
  bind_len := 0;
  nstates := 0;
  (* Bult-in kind for formulas *)
  Hashtbl.add kindTbl "o" (TPRED) ;
  (* Built-in types and kinds for systems' specification *)
  addKindTbl (TKIND("form")) ;
  addKindTbl (TKIND("term")) ;
  addTypeTbl "lft" (ARR (TBASIC (TKIND("form")), TBASIC (TPRED))) ;  (* type lft form -> o. *)
  addTypeTbl "rght" (ARR (TBASIC (TKIND("form")), TBASIC (TPRED))) ; (* type rght form -> o. *)
  (* \Gamma context (linear): stores the formulas that have no exponential *)
  Hashtbl.add !context "$gamma" [];
  Hashtbl.add subexTpTbl "$gamma" (LIN);
  (* \infty context (classical): stores specifications *)
  Hashtbl.add !context "$infty" [];
  Hashtbl.add subexTpTbl "$infty" (UNB)
;;

(*  Some examples on how things are inserted in the hashtables.
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
                      
