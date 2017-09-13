
(* Takes a system's specification in sellf (i.e. linear logic formulas) and
 * transforms into a specification in Coq using Carlos and Bruno's LL encoding
 * (https://github.com/meta-logic/coq-ll)
 **)

open Types

let preamble = "
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Add LoadPath \"../../\".
Require Export Permutation.
Require Export LL.SequentCalculi.
Require Export LL.StructuralRules.
Require Export LL.Multisets.
Require Export LL.StrongInduction.

Hint Resolve Max.le_max_r.
Hint Resolve Max.le_max_l.
"
;;

let beginModule = "
(* Specifying the Object Logic *)
Module PL.
"
;;

let syntax types = 
  let rec toCoqType tp = match tp with
    | TCONST (t) -> begin match t with
      | TKIND (s) -> begin match s with
        | "form" -> "LForm"
        | "term" -> "LTerm" (* TODO: check this name *)
        | _ -> s
      end
      | TINT -> "nat"
      | TSTRING -> "string"
      | _ -> failwith ("[ERROR] Unsupported type in Coq specification: " ^ (Prints.basicTypeToString t))
    end
    | TVAR (t) -> failwith "[ERROR] No type variables allowed in Coq declaration?"
    | ARR (t1, t2) -> (toCoqType t1) ^ " -> " ^ (toCoqType t2)
  in
  let declareTypes types = List.fold_right (fun (name, tp) acc ->
    "  | " ^ name ^ " : " ^ (toCoqType tp) ^ "\n" ^ acc
  ) types "" 
  in
(* Atomic propositions are always declared *)
  "
  (* !SD!: SYNTAX *)
  Inductive LForm :Set :=
  | atom : nat -> LForm (* atomic propositions are named with a natural number *)
" ^
  declareTypes types
  ^ "  .\n"
;;

(* TODO: this proof will change depending on the object logic *)
let formEqDecidability = "
  (* This theorem is needed in Multisets. I can see some difficulties:
     - It may rely on decidability of other types (e.g., Nat in this case 
     - The cases as conj seems to be solvable automatically (as done below )
   *)
  (* !SD! *)
  Theorem LForm_dec_eq : forall F G : LForm, {F = G} + {F <> G}.
    induction F;destruct G;
      try(right;discriminate); (* case equal *)
      try(match goal with [|- {?X =  ?X } + {?X <> ?X}] => left;auto end); (* case different *)
    try( (* inductive cases *)
        generalize(IHF1 G1);intro;
        generalize(IHF2 G2);intro;
        destruct H;destruct H0;subst;try(right;intro;inversion H;contradiction);auto).
    (* The hard part...relying on decidability of other datatypes *)
    generalize(eq_nat_decide n n0);intro Hn.
    destruct Hn.
    apply eq_nat_is_eq in e;subst;auto.
    right; intro;rewrite eq_nat_is_eq in n1.
    inversion H.
    contradiction.
  Qed.
" 

let multisetOLFormulas = "
  (* ========================================*)
  (* !SI!: Some definitions in order to define multisets on object level formulas
   * I assume that the object logic (always) uses multisets to represent contexts *)
  Module F_dec <: Eqset_dec_pol.
    Definition A := LForm.
    Definition eqA_dec := LForm_dec_eq.
    Fixpoint isPositive (n:nat) :=
      match n with
      | 0%nat => false
      | 1%nat => true
      | S (S n) => isPositive n
      end.
  End F_dec.

  Declare Module MSFormulas : MultisetList F_dec.
  Export MSFormulas.
  (* ========================================*)
"
;;

(* TODO: these are the object logic rules. We can probably get them from Leo's rewrite algorithm. *)
let rules spec = "
  (* ========================================*)
  (* RULES *)
  (* This should be straightforward from the rules of the system *)
  Reserved Notation \" L ';' n '|-P-' F\" (at level 80).
  Inductive sq : list LForm -> nat -> LForm -> Prop := 
    | dummy : [] ; 0 |-P- atom 0" ^
  "
  (* TODO: compute bipoles -> translate to obj. logic rules -> translate to Coq *)" ^
  (* EXAMPLE:
  | init : forall (L L' :list LForm) a, L =mul= atom a :: L' -> L ; 0 |-P- atom a
  | botL : forall (L L' :list LForm) G , L =mul= bot :: L' -> L ; 0 |-P- G
  | cR : forall L F G n m , L ; n |-P- F -> L ; m |-P- G -> L ; S (max n m) |-P- conj F G
  | cL : forall L G G' F L' n, L =mul= (conj G G') :: L' -> G :: G' :: L' ; n |-P- F -> L ; S n |-P- F

  REMINDERS:
    - Use multi-set equals (L =mul= F :: L') on the conclusion's context to
      incorporate exchange
    - Add height of the derivation, using 'max' for binary rules (n |-P-)
    - rg and lf must be odd numbers, other predicates can be any number (might
      not be relevant for this part specifically, but for smt later)
  *)
  "
  where \"L ; n |-P- F\" := (sq L n F).
  (* ========================================*)
"
;;

(* TODO: this proof will change depending on the object logic *)
let exchange = "
  (* !SD!: Exchange *)
  (* This Theorem is needed in one of the cases for Completeness. *)
  (* This theorem also looks difficult to generalize to arbitrary systems *)
  Theorem Exch : forall L L' F n, L =mul= L' -> L ; n |-P-F -> L' ;n  |-P-F.
    intros.
    generalize dependent L.
    generalize dependent L'.
    generalize dependent F.
    induction n using strongind;intros;subst.
    + (* base *)
      inversion H0;subst.
      rewrite H in H1.
      eapply init;auto.
      
      rewrite H in H1.
      eapply botL;auto.
    + (* inductive *)
      inversion H1;subst.
      
      (* cR *) 
      apply cR.
      eapply H with (L:=L);auto.
      eapply H with (L:=L);auto.
      
      (* cL *)
      rewrite H0 in H3.
      eapply cL;auto.
  Qed.
"
;;


let multisetLemmas = "
  (* !SI! *)
  (* Some Multiset stuff that we may later improve *)
  Lemma Contradiction_mset : forall a L,  meq []  (a :: L) -> False.
    intros.
    contradiction_multiset.
  Qed.
  Lemma Contradiction_mset' : forall a L,  meq  (a :: L) [] -> False.
    intros.
    symmetry in H.
    contradiction_multiset.
  Qed.
  
  Definition meqPL := meq.
"
;;

let endModule = "
End PL.
";;

(*
 * types : (string, type) list
 * spec : terms list
 **)
let sellf2coq types spec = 
  preamble ^
  beginModule ^
  syntax types ^
  formEqDecidability ^
  multisetOLFormulas ^
  rules spec ^
  exchange ^
  multisetLemmas ^
  endModule
