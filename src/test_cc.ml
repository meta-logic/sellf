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

(* test cut coherence  *)
let test1_cc test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/g1m" in
  let spec = FileParser.parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.cutCoherence specName spec);;

let test2_cc test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/lal" in
  let spec = FileParser.parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.cutCoherence specName spec);;

let test3_cc test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/lj" in
  let spec = FileParser.parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.cutCoherence specName spec);;

let test4_cc test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/lk" in
  let spec = FileParser.parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.cutCoherence specName spec);;

let test5_cc test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/ll" in
  let spec = FileParser.parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.cutCoherence specName spec);;


let test6_cc test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/ill" in
  let spec = FileParser.parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.cutCoherence specName spec);;

let test7_cc test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/mlj" in
  let spec = FileParser.parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.cutCoherence specName spec);;

let test8_cc test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/s4" in
  let spec = FileParser.parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.cutCoherence specName spec);;

let test9_cc test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/g3k" in
  let spec = FileParser.parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.cutCoherence specName spec);;


let test10_cc test_ctxt = 
  initAll();
  let fileName = "../examples/proofsystems/lax" in
  let spec = FileParser.parse fileName in
  let idx = String.rindex fileName '/' in
  let specName = Str.string_after fileName (idx+1) in 
    assert_equal true (Coherence.cutCoherence specName spec);;

