open OUnit
open Sigma

(* Eval tests *)
let eval_suite = "eval Unit Tests" >:::
  []

let _ = run_test_tt_main eval_suite



(* free_vars tests *)
let free_vars_suite = "free_vars Unit Tests" >:::
  []

let _ = run_test_tt_main free_vars_suite



(* size tests *)
let size_suite = "size Unit Tests" >:::
  []


(* typecheck tests *)
let typecheck_suite = "typecheck Unit Tests" >:::
  []

let _ = run_test_tt_main typecheck_suite

(* expand_synth_problem_typ tests *)
let expand_synth_problem_typ_suite = "expand_synth_problem_typ Unit Tests" >:::
  []

let _ = run_test_tt_main expand_synth_problem_typ_suite


(* Sigma tests *)
let test_sigma_lookup_ctor_empty _ =
          assert_equal
              (Sigma.lookup_ctor "Left" Sigma.empty)
                  (None)

let sigma_suite = "Sigma Unit Tests" >:::
  ["test_sigma_lookup_ctor_empty" >:: test_sigma_lookup_ctor_empty]

let _ = run_test_tt_main sigma_suite
