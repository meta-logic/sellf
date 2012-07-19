(*
 * A hashtable implements the context of a sequent. The key is the
 * name of the subexponential, and this is mapped to a list of formulas.
 * The linear formulas (not marked with ?l) are stored with the key '$gamma'.
 * The formulas of specification of systems are stored with the key '$infty'
 *
 * Giselle Machado Reis - 2012
 *)

open Basic
open Term
open Subexponentials
open Prints

(* Initial context, will be set depending on what we want to prove *)
let initial : (string, terms list) Hashtbl.t = Hashtbl.create 100 ;;

(* This holds the formulas that could be consumed by a top rule *)
let erasableByTop : (string, terms list) Hashtbl.t ref = ref (Hashtbl.create 100) ;;

let initSubexp s = Hashtbl.add initial s [] ;;

let store form subexp = try match Hashtbl.find initial subexp with
  | l -> Hashtbl.replace initial subexp (form :: l)
  with Not_found -> failwith ("Subexponential "^subexp^" not in context.")
;;

(* Clears all subexponentials *)
let clearInitial () = Hashtbl.iter (fun k d -> Hashtbl.replace initial k []) initial;;

(* Create proper contexts for each functionality of the system *)

let createCutCoherenceContext () = 
  (* Adding cut rules' specifications *)
  List.iter (fun e -> store e "$infty") !Term.cutRules ;;
  
let createInitialCoherenceContext () = 
  (* Adding identity rules' specifications *)
  List.iter (fun e -> store e "$infty") !Term.ids ;;
  
let createProofSearchContext () = 
  (* Adding rules' specifications (proof search without cut) *)
  List.iter (fun e -> store e "$infty") !Term.ids;
  List.iter (fun e -> store e "$infty") !Term.introRules;
  List.iter (fun e -> store e "$infty") !Term.structRules ;;
 
module Context = 
  struct
  
  type context = {
    hash : (string, terms list) Hashtbl.t;
  }

(* TODO create this type latter for derivations 
  type context_schema = {
    hash : (string, int) Hashtbl.t;
  }
*)

  (* Creates an empty context *)
  let createEmpty () = {
    hash = Hashtbl.create 100
  }

  let create h = {
    hash = h
  }

  (* Initialize a context with the formulas parsed *)
  let getInitial () = create initial

  let initialize () =
    (* \Gamma context (linear): stores the formulas that have no exponential *)
    initSubexp "$gamma";
    (* \infty context (classical): stores specifications *)
    initSubexp "$infty"

  (* All methods that operate on the context should return a new context with the proper modifications *)

  (* Adds a formula to a context *)
  let add ctx form subexp = 
    try match Hashtbl.find ctx.hash subexp with
      | forms -> 
        let newctx = Hashtbl.copy ctx.hash in
        Hashtbl.replace newctx subexp (form :: forms); 
        create newctx
      with Not_found -> failwith ("Subexponential "^subexp^" not in context.")

  (* Removes a formula (if it is linear) *)
  let remove ctx form subexp = 
    match type_of subexp with
      | LIN | AFF ->
        let newctx = Hashtbl.copy ctx.hash in
        let forms = Hashtbl.find newctx subexp in
        (* Removes the first occurence of form on the list. This can be implemented better *)
        let newforms = remove form forms in
        Hashtbl.replace newctx subexp newforms;
        create newctx
      | UNB | REL -> create (Hashtbl.copy ctx.hash)
  
  (* Delets a formula (unconditional) *)
  let delete ctx form subexp = try 
    let newctx = Hashtbl.copy ctx.hash in
    let forms = Hashtbl.find newctx subexp in
    (* Removes the first occurence of form on the list. This can be implemented better *)
    let newforms = Basic.remove form forms in
    Hashtbl.replace newctx subexp newforms;
    create newctx
    with _ -> 
      print_endline ("Trying to delete "^(termToString form)^" from "^subexp^" in:");
      print_endline ("CONTEXT\n"^(Hashtbl.fold (fun k d acc -> "["^k^"] "^(termsListToString d)^"\n"^acc) ctx.hash ""));
      failwith "Exception on deletion of formula from the context. "

  (* Returns the input context for the application of bang *)
  let bangin ctx subexp = 
    let newctx = Hashtbl.copy ctx.hash in
    Hashtbl.iter (fun idx forms ->
      match idx with
        (* Unbouded context  *)
        | "$infty" -> ()
        (* For every subexponential s < s holds. *)
        | s when s = subexp -> ()
        (* Formulas with no exponential must be erased *)
        | "$gamma" -> Hashtbl.replace newctx "$gamma" []
        (* These are deleted independently of being linear or classical *)
        | s -> 
          if not (greater_than s subexp) then Hashtbl.replace newctx s []
    ) ctx.hash;
    create newctx

  (* Returns the output context for the application of bang *)
  let bangout ctx subexp = 
    let newctx = Hashtbl.copy ctx.hash in
    Hashtbl.iter (fun idx forms ->
      match idx with
        (* These will always go to the out context  *)
        | "$gamma" | "$infty" -> ()
        | s -> match type_of s with
          (* Linear formulas that were in the input should not be available here. *)
          | LIN | AFF ->
            if (greater_than s subexp) || (s = subexp) then 
              Hashtbl.replace newctx s []
          (* Classical formulas are always available *)
          | UNB | REL -> ()
    ) ctx.hash;
    create newctx

  (* TODO: implement equality *)
  let equals ctx1 ctx2 = true 

  (* Checks if all linear contexts are empty (ignoring the formulas that could
  be erased by a top rule) *)
  let isLinearEmpty ctx = List.length ( 
    Hashtbl.fold (fun idx forms acc ->
      match type_of idx with
        | LIN | AFF -> begin 
          (* Finds the formulas that could be erased by top *)
          try match Hashtbl.find !erasableByTop idx with
            | erasable ->
              let newforms = List.filter (fun e -> not (List.mem e erasable)) forms in
              newforms @ acc
            with Not_found -> forms @ acc
        end
        | UNB | REL -> acc
    ) ctx.hash [] 
  ) == 0

  (* Marks the formulas of this context as erasable because a top rule was
  applied. *)
  let markErasable ctx = Hashtbl.iter (fun idx forms ->
    try match Hashtbl.find !erasableByTop idx with
      | formlst ->
        Hashtbl.replace !erasableByTop idx (formlst @ forms); 
      with Not_found -> Hashtbl.add !erasableByTop idx forms;
  ) ctx.hash

  (* Merges two contexts *)
  let merge ctx1 ctx2 = 
    let newctx = Hashtbl.copy ctx1.hash in
    Hashtbl.iter (fun idx forms ->
      match type_of idx with
        | LIN | AFF -> (
          try match Hashtbl.find newctx idx with
            | f -> Hashtbl.replace newctx idx (forms @ f)
          with Not_found -> failwith "Trying to merge two contexts with different subexponentials"
          )
        | UNB | REL -> ()
    ) ctx2.hash;
    create newctx

  let toPairs ctx = Hashtbl.fold (fun key data acc -> 
    let rec pairs k lst = match lst with
      | [] -> []
      | elm :: tl -> (k, elm) :: pairs k tl
    in
    (pairs key data) @ acc
    ) ctx.hash []

  let toString ctx = "CONTEXT\n"^(Hashtbl.fold (fun k d acc -> "["^k^"] "^(termsListToString d)^"\n"^acc) ctx.hash "")

  end
;;
