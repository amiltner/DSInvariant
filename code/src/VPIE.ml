open MyStdlib
open Verifiers
open Lang

module Make(V : Verifier) =
struct
  let learnVPreCond
      ~(problem:problem)
      ~(pre:Expr.t)
      ~(eval : Expr.t)
      ~(eval_t : Type.t)
      ~(post : UniversalFormula.t)
      ~(positives : Value.t list)
    : Expr.t =
    let testbed = TestBed.create_positive positives in
    let rec helper
        (attempt:int)
        (testbed:TestBed.t)
      : Expr.t =
        (Log.info (lazy ("VPIE Attempt "
                         ^ (Int.to_string attempt)
                         ^ "."));
         let pos_examples = List.map ~f:(fun (v,_) -> v) testbed.pos_tests in
         let neg_examples = List.map ~f:(fun (v,_) -> v) testbed.neg_tests in
         let subvalues =
           List.concat_map
             ~f:Value.strict_subvalues
             (pos_examples@neg_examples)
         in
         let all_inside_examples =
           List.filter
             ~f:(fun e ->
                 Typecheck.type_equiv
                   problem.tc
                   (Type.mk_var "t")
                   (Typecheck.typecheck_exp problem.ec problem.tc problem.vc (Value.to_exp e)))
             subvalues
         in
         let temp_testbed =
           List.fold_left
             ~f:(fun tb e ->
                 if Option.is_some
                     (V.true_on_examples
                        ~problem
                        ~examples:[e]
                        ~eval:eval
                        ~eval_t
                        ~post:post) then
                   TestBed.add_neg_test_allow_dups ~testbed:tb e
                 else
                   TestBed.add_pos_test_allow_dups ~testbed:tb e
              )
             ~init:testbed
             all_inside_examples
           in
         let synthed_pre = Expr.simplify @$ Option.value_exn (V.synth ~problem ~testbed:temp_testbed) in
         Log.info (lazy ("Candidate Precondition: " ^ (Expr.show synthed_pre)));
         let full_pre = Expr.and_predicates pre synthed_pre in
         begin match V.implication_counter_example ~problem ~pre:full_pre ~eval ~eval_t ~post with
           | None ->
             Log.info (lazy ("Verified Precondition: " ^ (Expr.show synthed_pre)));
             full_pre
           | Some model ->
             if (List.length model <> 1) then
               failwith ("cannot do such functions yet: " ^ (string_of_list Value.show model))
             else
               helper
                 (attempt+1)
                 (TestBed.add_neg_test_disallow_dups
                    ~testbed
                    (List.hd_exn model))
           end)
    in
    helper 0 testbed
end
