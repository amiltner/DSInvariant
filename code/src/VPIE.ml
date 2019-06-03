open MyStdlib
open Lang

module Make (V : Verifier.t) (S : Synthesizer.t) = struct
  let learnVPreCondAll
      ~(problem : problem)
      ~(pre : Expr.t)
      ~(post : UniversalFormula.t)
      ~(positives : Value.t list)
    : Expr.t =
    let testbed = TestBed.create_positive positives in
    let model_o =
      List.fold_left
        ~f:(fun acc (eval,eval_t) ->
            begin match acc with
              | None ->
                V.implication_counter_example
                  ~problem
                  ~pre:pre
                  ~eval
                  ~eval_t
                  ~post
              | Some _ -> acc
            end)
        ~init:None
        problem.mod_vals
    in
    if Option.is_none model_o then
      Expr.mk_constant_true_func Type.mk_t_var
    else
      let rec helper
          (attempt:int)
          (testbed:TestBed.t)
        : Expr.t =
        (Log.info (lazy ("VPIE Attempt "
                         ^ (Int.to_string attempt)
                         ^ "."));
         let subvalues =
           List.concat_map
             ~f:Value.strict_subvalues
             (testbed.pos_tests @ testbed.neg_tests)
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
                   TestBed.add_neg_test ~testbed:tb e
                 else
                   TestBed.add_pos_test ~testbed:tb e
               )
             ~init:testbed
             all_inside_examples
         in
         print_endline (TestBed.show testbed);
         let synthed_pre = Expr.simplify @$ Option.value_exn (S.synth ~problem ~testbed:testbed) in
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
             full_pre
           | Some model ->
             if (List.length model <> 1) then
               failwith ("cannot do such functions yet: " ^ (string_of_list Value.show model))
             else
               let new_neg_example = List.hd_exn model in
               Log.info (lazy ("Add negative example: " ^ (Value.show new_neg_example)));
               helper (attempt+1) (TestBed.add_neg_test ~testbed new_neg_example)
         end)
      in
      helper 0 testbed

  let learnVPreCond
      ~(problem:problem)
      ~(pre:Expr.t)
      ~(eval : Expr.t)
      ~(eval_t : Type.t)
      ~(post : UniversalFormula.t)
      ~(positives : Value.t list)
    : Expr.t =
    let testbed = TestBed.create_positive positives in
    let model_o =
      List.fold_left
        ~f:(fun acc (eval,eval_t) ->
            begin match acc with
              | None ->
                V.implication_counter_example
                  ~problem
                  ~pre:pre
                  ~eval
                  ~eval_t
                  ~post
              | Some _ -> acc
            end)
        ~init:None
        problem.mod_vals
    in
    if Option.is_none model_o then
      Expr.mk_constant_true_func Type.mk_t_var
    else
    let rec helper
        (attempt:int)
        (testbed:TestBed.t)
      : Expr.t =
      (Log.info (lazy ("VPIE Attempt "
                       ^ (Int.to_string attempt)
                       ^ "."));
       let subvalues =
         List.concat_map
           ~f:Value.strict_subvalues
           (testbed.pos_tests @ testbed.neg_tests)
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
                 TestBed.add_neg_test ~testbed:tb e
               else
                 TestBed.add_pos_test ~testbed:tb e
             )
           ~init:testbed
           all_inside_examples
       in
       print_endline (TestBed.show testbed);
       let synthed_pre = Expr.simplify @$ Option.value_exn (S.synth ~problem ~testbed:testbed) in
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
           full_pre
         | Some model ->
           if (List.length model <> 1) then
             failwith ("cannot do such functions yet: " ^ (string_of_list Value.show model))
           else
             let new_neg_example = List.hd_exn model in
             Log.info (lazy ("Add negative example: " ^ (Value.show new_neg_example)));
             helper (attempt+1) (TestBed.add_neg_test ~testbed new_neg_example)
       end)
    in
    helper 0 testbed
end
