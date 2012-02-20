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

(* This is to be used by the parser. Initially, all the formulas are stored here. *)
let initial : (string, terms list) Hashtbl.t = Hashtbl.create 100 ;;

let initSubexp s = Hashtbl.add initial s [] ;;

let store form subexp = try match Hashtbl.find initial subexp with
  | l -> Hashtbl.replace initial subexp (form :: l)
  with Not_found -> failwith ("Subexponential "^subexp^" not in context.")
;;

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

  (* All methods that operate on the contextshould return a new context with the proper modifications *)

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
          if not (greater_than idx s) then Hashtbl.replace newctx s []
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
            if (greater_than idx s) || (s = subexp) then Hashtbl.replace newctx s []
          (* Classical formulas are always available *)
          | UNB | REL -> ()
    ) ctx.hash;
    create newctx

  (* TODO: implement equality *)
  let equals ctx1 ctx2 = true 

  (* Checks if all linear contexts are empty *)
  let isLinearEmpty ctx = List.length ( 
    Hashtbl.fold (fun idx forms acc ->
      match type_of idx with
        | LIN | AFF -> forms @ acc
        | UNB | REL -> acc
    ) ctx.hash [] 
  ) == 0

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
