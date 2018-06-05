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
 "test10_cc">:: Test_cc.test10_cc;


 (* Testing initial coherence *)
  "test1_ic">:: Test_ic.test1_ic;
  "test2_ic">:: Test_ic.test2_ic;
  "test3_ic">:: Test_ic.test3_ic;
  "test4_ic">:: Test_ic.test4_ic;
  "test5_ic">:: Test_ic.test5_ic;
  "test6_ic">:: Test_ic.test6_ic;
  "test7_ic">:: Test_ic.test7_ic;
  "test8_ic">:: Test_ic.test8_ic;
  "test9_ic">:: Test_ic.test9_ic;
  "test9_ic">:: Test_ic.test10_ic;
 
 (* Testing principal cut *)
  "test1_pc">:: Test_pc.test1_pc;
  "test2_pc">:: Test_pc.test2_pc;
  "test3_pc">:: Test_pc.test3_pc;
  "test4_pc">:: Test_pc.test4_pc;
  "test5_pc">:: Test_pc.test5_pc;
  "test6_pc">:: Test_pc.test6_pc;
  "test7_pc">:: Test_pc.test7_pc;
  "test8_pc">:: Test_pc.test8_pc;
  "test9_pc">:: Test_pc.test9_pc;
  "test10_pc">:: Test_pc.test10_pc;

 (* Testing atomicelim *)

  "test1_at">:: Test_at.test1_at;
  "test2_at">:: Test_at.test2_at;
  "test3_at">:: Test_at.test3_at;
  "test4_at">:: Test_at.test4_at;
  "test5_at">:: Test_at.test5_at;
  "test6_at">:: Test_at.test6_at;
  "test7_at">:: Test_at.test7_at;
  "test8_at">:: Test_at.test8_at;
  "test9_at">:: Test_at.test9_at;
  "test10_at">:: Test_at.test10_at

  (* Testing permutations *)
  (*"test_pr_ll">:: Test_pr.test_pr_0*)
  (*"test_pr_lj">:: Test_pr_lj.test_pr_lj*)
  (*"test_pr_lj">:: Test_pr.test_pr_lj;*)
  (*"test_pr_mlj">:: Test_pr.test_pr_mlj*)
  ]
;;


let () =
  run_test_tt_main suite
;;
