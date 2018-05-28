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

let check_initialcoherence system_name = Coherence.initialCoherence_t system_name ;;

(* Test initial coherence *)

let test1_ic test_ctxt = 
  initAll();
  let fileName = ref "../examples/proofsystems/g1m";
       in
    let idx = String.rindex !fileName '/' in
      let specName = Str.string_after !fileName (idx+1) in 
        assert_equal 1 (check_initialcoherence specName);;

