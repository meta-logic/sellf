open OUnit2
open Bipole
open Context
open ProofTree
open Subexponentials
open Specification
open Prints
open OlRule
open ProofTreeSchema
open Permutation

let initAll () = 
  Context.initialize ();
  Subexponentials.initialize ();
;;

(* test atomicelim *)
let test1_at test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/g1m" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test2_at test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/lal" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test3_at test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/lax" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test4_at test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/lj" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test5_at test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/lk" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test6_at test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/ll" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test7_at test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/ill" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;;

let test8_at test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/mlj" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;; 

let test9_at test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/s4" in
  assert_equal true (Staticpermutationcheck.weak_coherent spec)
;; 

let test10_at test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/g3k" in
  assert_equal false (Staticpermutationcheck.weak_coherent spec)
;;

