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
 "test6_cc">:: Test_cc.test6_cc;
 "test7_cc">:: Test_cc.test7_cc;
 "test8_cc">:: Test_cc.test8_cc;
 "test9_cc">:: Test_cc.test9_cc;


 (* Testing initial coherence *)
  "test1_ic">:: Test_ic.test1_ic;
  "test2_ic">:: Test_ic.test2_ic;
  "test3_ic">:: Test_ic.test3_ic;
  "test4_ic">:: Test_ic.test4_ic;
  "test5_ic">:: Test_ic.test5_ic;
  "test6_ic">:: Test_ic.test6_ic;
  "test7_ic">:: Test_ic.test7_ic;
  "test8_ic">:: Test_ic.test8_ic;
  "test9_ic">:: Test_ic.test9_ic

  ]
;;


let () =
  run_test_tt_main suite
;;
