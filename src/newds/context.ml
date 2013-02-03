(**************************************)
(*                                    *)
(*       Context for sequents         *)
(*                                    *)
(*  Giselle Machado Reis              *)
(*  2013                              *)
(*                                    *)
(**************************************)

(* TODO: write interface *)
(* TODO: rewrite printing methods *)

type abstractContext = {
  aHash : (string, int) Hashtbl.t
}

(* Holds the indices of the context variables *)
let global : (string, int) Hashtbl.t = Hashtbl.create 100 ;;

type concreteContext = {
  cHash : (string, term lst) Hashtbl.t
}

type context = 
  | ABSCTX of abstractContext
  | CONCTX of concreteContext

let createAbs () = { 
  aHash = Hashtbl.create 100;
  let subexps = keys subexTpTbl in
  List.iter (fun s -> Hashtbl.add aHash s 0; Hashtbl.add global s 0) subexps;
  ctx
}


