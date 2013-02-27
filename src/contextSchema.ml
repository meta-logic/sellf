(*****************************************)
(*                                       *)
(*          Generic context              *)
(*                                       *)
(*  Giselle Machado Reis                 *)
(*  2013                                 *)
(*                                       *)
(*****************************************)

open Prints

let global : (string, int) Hashtbl.t = Hashtbl.create 100 ;;

type context = {
  hash : (string, int) Hashtbl.t;
}

(*
let create () = { 
  hash = Hashtbl.create 100
}
*)

let create h = {
  hash = h
}

let createFresh () = 
  let subexps = Subexponentials.getAll () in
  let fresh = Hashtbl.create 100 in
  List.iter ( fun s ->
    let n = Hashtbl.find global s in
    Hashtbl.replace global s (n+1);
    Hashtbl.add fresh s n;
  ) subexps;
  create fresh

(*
let initialize ctx = 
  let subexps = Subexponentials.getAll () in
  List.iter (fun s -> Hashtbl.add ctx.hash s 0; Hashtbl.add global s 0) subexps;
  ctx
*)

let copy ctx = create (Hashtbl.copy ctx.hash)

let getIndex ctx s = try match Hashtbl.find ctx.hash s with
  | i -> i
  with Not_found -> failwith ("Subexponential "^s^" not in context.")

let getContexts ctx = Hashtbl.fold (fun k v acc -> (k, v) :: acc) ctx.hash []

let toString ctx = Hashtbl.fold (fun n i acc -> n ^ "_" ^ (string_of_int i) ^ ", " ^ acc) ctx.hash ""

let toTexString ctx = Hashtbl.fold (fun n i acc -> "\\Gamma_{" ^ (remSpecial n) ^ "}^{" ^ (string_of_int i) ^ "} ; " ^ acc) ctx.hash ""

let ctxToTex (s, i) = 
  let news = remSpecial s in
  ("\\Gamma_{"^news^"}^{"^(string_of_int i)^"}")

let ctxToStr (s, i) = 
  let news = remSpecial s in
  ""^news^"_"^(string_of_int i)^""

(* Creates the next context where the index of subexp is updated *)
let next ctx subexp =
  let index = Hashtbl.find global subexp in
  let newctxhash = Hashtbl.copy ctx.hash in
  Hashtbl.replace newctxhash subexp (index + 1);
  Hashtbl.replace global subexp (index + 1);
  create newctxhash

(* Creates the next context after inserting a formula in subexp *)
let insert ctx subexp = 
  let index = Hashtbl.find global subexp in
  let newctxhash = Hashtbl.copy ctx.hash in
  Hashtbl.replace newctxhash subexp (index+2);
  Hashtbl.replace global subexp (index+2);
  create newctxhash

(* Creates the two resulting contexts after a split *)
let split ctx = 
  let hashctx1 = Hashtbl.copy ctx.hash in
  let hashctx2 = Hashtbl.copy ctx.hash in
  Hashtbl.iter (fun s i -> match Subexponentials.type_of s with
    | Subexponentials.LIN | Subexponentials.REL -> 
      (* Global number for this subexponential *)
      let n = Hashtbl.find global s in
      (* Updating the global counter of s *)
      Hashtbl.replace global s (n+2);
      (* Configuring a new s context for each branch *)
      Hashtbl.replace hashctx1 s (n+1);
      Hashtbl.replace hashctx2 s (n+2);
    | Subexponentials.UNB | Subexponentials.AFF -> ()
  )  ctx.hash;
  (create hashctx1, create hashctx2)

(* Creates the resulting context after a bang - increments the indices of
those contexts that have their formulas erased *)
let bang ctx subexp = 
  let hashctx = Hashtbl.copy ctx.hash in
  Hashtbl.iter (fun s i -> match Subexponentials.type_of s with
    | Subexponentials.LIN | Subexponentials.REL -> ()
    | Subexponentials.UNB | Subexponentials.AFF -> 
      if s = subexp || (Subexponentials.greater_than s subexp) then ()
      else begin
        let n = Hashtbl.find global s in
        Hashtbl.replace global s (n+1);
        Hashtbl.replace hashctx s (n+1)
      end
  ) ctx.hash;
  create hashctx


