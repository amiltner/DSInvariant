open MyStdlib
open Lang

module Make(V : Verifier.t) =
struct
  let negs : Value.t list ref = ref []

  let satisfies_testbed
      ~(problem:problem)
      (tb:TestBed.t)
      (e : Expr.t)
    : bool =
    let positives = List.map ~f:fst tb.pos_tests in
    let negatives = List.map ~f:fst tb.neg_tests in
    List.for_all
      ~f:(fun p ->
          let ans =
            Eval.evaluate_with_holes
              ~eval_context:problem.eval_context
              (Expr.mk_app e (Value.to_exp p))
          in
          is_equal @$
          Value.compare
            ans
            Value.mk_true)
      positives
      &&
      List.for_all
        ~f:(fun p ->
            let ans =
              Eval.evaluate_with_holes
                ~eval_context:problem.eval_context
                (Expr.mk_app e (Value.to_exp p))
            in
            is_equal @$
            Value.compare
              ans
              Value.mk_false)
        negatives

  let learnVPreCondAll
      ~(problem : problem)
      ~(pre : Expr.t)
      ~(post : UniversalFormula.t)
      ~(positives : Value.t list)
    : Expr.t =
    let rec helper
        (attempt:int)
        (testbed:TestBed.t)
        (pres:Expr.t list)
      : Expr.t =
      (Log.info (lazy ("VPIE Attempt "
                       ^ (Int.to_string attempt)
                       ^ "."));
       let pres =
         begin match List.filter ~f:(satisfies_testbed ~problem testbed) pres with
           | [] ->
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
             let testbed =
               List.fold_left
                 ~f:(fun tb e ->
                     if Option.is_some
                         (V.true_on_examples
                            ~problem
                            ~examples:[e]
                            ~eval:(Expr.mk_identity_func (Type.mk_var "t"))
                            ~eval_t:(Type.mk_arr (Type.mk_var "t") (Type.mk_var "t"))
                            ~post:post) then
                       TestBed.add_neg_test_allow_dups ~testbed:tb e
                     else
                       TestBed.add_pos_test_allow_dups ~testbed:tb e
                   )
                 ~init:testbed
                 all_inside_examples
             in
             List.map ~f:Expr.simplify (V.synth ~problem ~testbed:testbed)
           | pres ->
             pres
         end
       in
       let synthed_pre = List.hd_exn pres in
       Log.info (lazy ("Candidate Precondition: " ^ (Expr.show synthed_pre)));
       let full_pre = Expr.and_predicates pre synthed_pre in
       let model_o =
         List.fold_left
           ~f:(fun acc (eval,eval_t) ->
               begin match acc with
                 | None ->
                   V.implication_counter_example
                     ~problem
                     ~pre:full_pre
                     ~eval
                     ~eval_t
                     ~post
                 | Some _ -> acc
               end)
           ~init:None
           problem.mod_vals
       in
       begin match model_o with
         | None ->
           Log.info (lazy ("Verified Precondition: " ^ (Expr.show synthed_pre)));
           synthed_pre
         | Some model ->
           if (List.length model <> 1) then
             failwith ("cannot do such functions yet: " ^ (string_of_list Value.show model))
           else
             let new_neg_example = List.hd_exn model in
             Log.info (lazy ("Add negative example: " ^ (Value.show new_neg_example)));
             helper
               (attempt+1)
               (TestBed.add_neg_test_disallow_dups
                  ~testbed
                  new_neg_example)
               pres
       end)
    in
    let testbed = TestBed.create_positive positives in
    helper 0 testbed [Expr.mk_constant_true_func Type.mk_t_var]

  let learnVPreCond
      ~(problem:problem)
      ~(pre:Expr.t)
      ~(eval : Expr.t)
      ~(eval_t : Type.t)
      ~(post : UniversalFormula.t)
      ~(positives : Value.t list)
    : Expr.t =
    let rec helper
        (attempt:int)
        (testbed:TestBed.t)
        (pres:Expr.t list)
      : Expr.t =
       let pres =
         begin match List.filter ~f:(satisfies_testbed ~problem testbed) pres with
           | [] ->
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
             let testbed =
               List.fold_left
                 ~f:(fun tb e ->
                     if Option.is_some
                         (V.true_on_examples
                            ~problem
                            ~examples:[e]
                            ~eval:(Expr.mk_identity_func (Type.mk_var "t"))
                            ~eval_t:(Type.mk_arr (Type.mk_var "t") (Type.mk_var "t"))
                            ~post:post) then
                       TestBed.add_neg_test_allow_dups ~testbed:tb e
                     else
                       TestBed.add_pos_test_allow_dups ~testbed:tb e
                   )
                 ~init:testbed
                 all_inside_examples
             in
             List.map ~f:Expr.simplify (V.synth ~problem ~testbed:testbed)
           | pres ->
             pres
         end
       in
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
       let testbed =
         List.fold_left
           ~f:(fun tb e ->
               if Option.is_some
                   (V.true_on_examples
                      ~problem
                      ~examples:[e]
                      ~eval:(Expr.mk_identity_func (Type.mk_var "t"))
                      ~eval_t:(Type.mk_arr (Type.mk_var "t") (Type.mk_var "t"))
                      ~post:post) then
                 TestBed.add_neg_test_allow_dups ~testbed:tb e
               else
                 TestBed.add_pos_test_allow_dups ~testbed:tb e
             )
           ~init:testbed
           all_inside_examples
       in
       let synthed_pre = List.hd_exn pres in
       Log.info (lazy ("Candidate Precondition: " ^ (Expr.show synthed_pre)));
       let full_pre = Expr.and_predicates pre synthed_pre in
       let model_o =
         V.implication_counter_example
           ~problem
           ~pre:full_pre
           ~eval
           ~eval_t
           ~post
       in
       begin match model_o with
         | None ->
           Log.info (lazy ("Verified Precondition: " ^ (Expr.show synthed_pre)));
           synthed_pre
         | Some model ->
           if (List.length model <> 1) then
             failwith ("cannot do such functions yet: " ^ (string_of_list Value.show model))
           else
             let new_neg_example = List.hd_exn model in
             negs := new_neg_example::!negs;
             Log.info (lazy ("Add negative example: " ^ (Value.show new_neg_example)));
             helper
               (attempt+1)
               (TestBed.add_neg_test_disallow_dups
                  ~testbed
                  new_neg_example)
               pres
       end)
    in
    let testbed = TestBed.create_positive positives in
    let testbed =
      List.fold
        ~f:(fun testbed n -> TestBed.add_neg_test_disallow_dups ~testbed n)
        ~init:testbed
        !negs
    in
    helper 0 testbed [Expr.mk_constant_true_func Type.mk_t_var]
end
