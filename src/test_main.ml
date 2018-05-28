open OUnit2
open Bipole
open Context
open ProofTree
open Subexponentials
open Prints
open OlRule
open ProofTreeSchema
open Permutation

let suite =
"suite">:::
 [

(* Testing cut coherence *)
 "test1_cc">:: Test_cc.test1_cc;
 "test2_cc">:: Test_cc.test2_cc;
 "test3_cc">:: Test_cc.test3_cc;
 "test4_cc">:: Test_cc.test4_cc;
 "test5_cc">:: Test_cc.test5_cc;


 (* Testing initial coherence *)
  "test1_ic">:: Test_ic.test1_ic

  ]
;;


let () =
  run_test_tt_main suite
;;
