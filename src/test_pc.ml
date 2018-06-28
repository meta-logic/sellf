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

(* Test principalcut *)
let test1_pc test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/g1m" in
  assert_equal true (Staticpermutationcheck.cut_principal spec)
;;

let test2_pc test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/lal" in
  assert_equal true (Staticpermutationcheck.cut_principal spec)
;; 

let test3_pc test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/lax" in
  assert_equal true (Staticpermutationcheck.cut_principal spec)
;; 

let test4_pc test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/lj" in
  assert_equal true (Staticpermutationcheck.cut_principal spec)
;; 

let test5_pc test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/lk" in
  assert_equal true (Staticpermutationcheck.cut_principal spec)
;; 

let test6_pc test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/ll" in
  assert_equal true (Staticpermutationcheck.cut_principal spec)
;; 

let test7_pc test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/ill" in
  assert_equal false (Staticpermutationcheck.cut_principal spec)
;; 

let test8_pc test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/mlj" in
  assert_equal false (Staticpermutationcheck.cut_principal spec)
;; 

let test9_pc test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/s4" in
  assert_equal false (Staticpermutationcheck.cut_principal spec)
;; 

let test10_pc test_ctxt = 
  initAll();
  let spec = FileParser.parse "../examples/proofsystems/g3k" in
  assert_equal false (Staticpermutationcheck.cut_principal spec)
;; 
