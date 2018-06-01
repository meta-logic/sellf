open OUnit2
open Bipole
open Context
open ProofTree
open Subexponentials
open Prints
open OlRule
open ProofTreeSchema
open Permutation

let initAll () = 
  Specification.initialize ();
  Context.initialize ();
  Subexponentials.initialize ();
;;

let check_cutcoherence system_name = Coherence.cutCoherence_t system_name ;;

(* test cut coherence  *)
let test1_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/g1m";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;

let test2_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/lal";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;

let test3_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/lj";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;

let test4_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/lk";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;

let test5_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/ll";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;


let test6_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/ill";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;

let test7_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/mlj";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;

let test8_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/s4";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;

let test9_cc test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/g3k";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_cutcoherence specName);;

