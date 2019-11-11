open Core

module Make (V : Verifier.t) (S : Synthesizer.t) (L : LR.t) = struct

  let negs : Value.t list ref = ref []
  let possibilities : Expr.t list ref = ref [Expr.mk_constant_true_func (Type._t)]

  let satisfies_testbed
      ~(problem:Problem.t)
      (tb:TestBed.t)
      (e : Expr.t)
    : bool =
    List.for_all
      ~f:(fun p ->
          let ans =
            Eval.evaluate_with_holes_basic
              ~tc:problem.tc
              ~eval_context:problem.eval_context
              (Expr.mk_app e (Value.to_exp p))
          in
          Value.equal
            ans
            Value.mk_true)
      tb.pos_tests
      &&
      List.for_all
        ~f:(fun p ->
            let ans =
              Eval.evaluate_with_holes_basic
                     ~tc:problem.tc
                ~eval_context:problem.eval_context
                (Expr.mk_app e (Value.to_exp p))
            in
            Value.equal
              ans
              Value.mk_false)
        tb.neg_tests

  let check_boundary
      ~(problem : Problem.t)
      ~(invariant : Expr.t)
      ~(positives : Value.t list)
    : Value.t list =
    let check_boundary_singleton
        ~(problem : Problem.t)
        ~eval:(eval : Expr.t)
        ~(eval_t : Type.t)
        ~post:(post : Value.t LR.condition)
        ~positives:(positives : Value.t list)
      : Value.t list * Value.t list =
      Log.info
        (lazy ("Checking boundary for:" ^ (DSToMyth.full_to_pretty_myth_string ~problem eval)));
      let m =
        L.verifier
          ~problem
          eval_t
          post
          (LR.Set positives)
          (Eval.evaluate_with_holes_basic ~tc:problem.tc ~eval_context:problem.eval_context eval)
      in
      begin match m with
        | ([],[]) ->
          Log.info (lazy ("Safe"));
          m
        | _ ->
          Log.info
            (lazy ("Boundary Not Satisfied, counterexample:"
                   ^ (Log.indented_sep 4)
                   ^ (List.to_string ~f:Value.show (snd m))
                   ^ (Log.indented_sep 4)
                   ^ "Comes from"
                   ^ (Log.indented_sep 4)
                   ^ (List.to_string ~f:Value.show (fst m)))) ;
          m
      end
    in
    let post =
      LR.Predicate
        (fun v ->
           Value.equal
             Value.mk_true
             (Eval.evaluate_with_holes_basic
                     ~eval_context:problem.eval_context
                     ~tc:problem.tc
                     (Expr.mk_app
                        invariant
                        (Value.to_exp v))))
    in
    snd
      (List.fold_left
         ~f:(fun acc (eval,eval_t) ->
             begin match acc with
               | ([],[]) ->
                 check_boundary_singleton
                   ~problem
                   ~eval
                   ~eval_t
                   ~post
                   ~positives
               | _ -> acc
             end)
         ~init:([],[])
         problem.mod_vals)

  let valid_answer_lists
      ~(problem:Problem.t)
      ~(answer_lists : (Expr.t * TestBed.t * Value.t list) list)
      ~(new_positives : Value.t list)
    : (Expr.t * TestBed.t * Value.t list) list =
    let answer_lists =
      List.filter_map
        ~f:(fun (e,tb,ces) ->
            Option.map
              ~f:(fun tb -> (e,tb,ces))
              (TestBed.add_pos_tests_safe ~testbed:tb new_positives))
        answer_lists
    in
    List.filter
      ~f:(fun (e,tb,_) -> satisfies_testbed ~problem tb e)
      answer_lists

  let synth_new_inv
      ~(problem:Problem.t)
      ~(testbed:TestBed.t)
    : Expr.t =
    begin match List.filter ~f:(satisfies_testbed ~problem testbed) !possibilities with
      | [] ->
        let subvalues =
          List.concat_map
            ~f:Value.strict_subvalues
            (testbed.pos_tests@testbed.neg_tests)
        in
        let all_inside_examples =
          List.filter
            ~f:(fun e ->
                Typecheck.type_equiv
                  problem.tc
                  (Type._t)
                  (Typecheck.typecheck_exp problem.ec problem.tc problem.vc (Value.to_exp e)))
            subvalues
        in
        (*let ps_t =
          List.filter
            ~f:(fun (_,t) -> Type.equal t Type._t)
            ps
        in
        assert (List.length ps_t = 1);
          let (t_p_i,_) = List.hd_exn ps_t in*)
        let testbed =
          List.fold_left
            ~f:(fun tb e ->
                if TestBed.contains_test ~testbed:tb e then
                  tb
                else
                  TestBed.add_neg_test ~testbed:tb e)
            ~init:testbed
            all_inside_examples
        in
        Log.info (lazy "testbed");
        Log.info (lazy (TestBed.show testbed));
        let results = snd (S.synth ~problem ~testbed:testbed) in
        let results =
          List.map
            ~f:(fun e -> assert (satisfies_testbed ~problem testbed e); Expr.simplify e)
            results
        in
        possibilities := results;
        List.hd_exn results
      | h::_ ->
        h
    end

  let verify_proves_post
      ~(problem:Problem.t)
      ~(invariant:Expr.t)
      ~(post:UniversalFormula.t)
    : Value.t list =
    Log.info (lazy ("verifying proves postcondition"));
    let vs =
      V.implication_counter_example
        ~problem
        ~pre:invariant
        ~eval:(Expr.mk_identity_func (Type._t))
        ~eval_t:(Type.mk_arrow (Type._t) (Type._t))
        ~post
    in
    begin match vs with
      | [] ->
        Log.info (lazy ("postcondition proven"));
        vs
      | _ ->
        Log.info (lazy ("postcondition unproven, counterexample: "
                       ^ (List.to_string ~f:Value.show vs)));
        vs
    end

  let verify_module
      ~(problem:Problem.t)
      ~(invariant:Expr.t)
    : Value.t list =
    let invariant_pred =
      LR.Predicate
        (fun v ->
           Value.equal
             Value.mk_true
             (Eval.evaluate_with_holes_basic
                     ~tc:problem.tc
                     ~eval_context:problem.eval_context
                     (Expr.mk_app
                        invariant
                        (Value.to_exp v))))
    in
    List.fold_left
      ~f:(fun acc (eval,eval_t) ->
          begin match acc with
            | [] ->
              Log.info (lazy ("verifying: " ^ DSToMyth.full_to_pretty_myth_string ~problem eval));
              let model =
                (L.verifier
                   ~problem
                   eval_t
                   invariant_pred
                   invariant_pred
                   (Eval.evaluate_with_holes_basic ~tc:problem.tc ~eval_context:problem.eval_context eval))
              in
              begin match model with
                | ([],[]) -> Log.info (lazy ("Safe")); fst model
                | _ ->
                  Log.info
                    (lazy ("Not a LR, counterexample:"
                           ^ (Log.indented_sep 4)
                           ^ (List.to_string ~f:Value.show (snd model))
                           ^ (Log.indented_sep 4)
                           ^ "Comes from"
                           ^ (Log.indented_sep 4)
                           ^ (List.to_string ~f:Value.show (fst model)))) ;
                  fst model
              end
            (*V.implication_counter_example
              ~problem
              ~pre:full_pre
              ~eval
              ~eval_t
              ~post*)
            | _ -> acc
          end)
      ~init:[]
      problem.mod_vals


  let learnVPreCondTrueAll
      ~(problem : Problem.t)
      ~(post : UniversalFormula.t)
    : Expr.t =
    let rec learnVPreCondTrueAllInternal
        ~(answer_lists : (Expr.t * TestBed.t * Value.t list) list)
      : Expr.t =
      Log.info (lazy ("Answer list length: " ^ (string_of_int (List.length answer_lists))));
      begin match answer_lists with
        | [] -> failwith "something went drastically wrong"
        | (invariant,testbed,ces)::answer_lists ->
          let old_invariant = invariant in
          let old_testbed = testbed in
          Log.info (lazy ("Candidate invariant: " ^ (DSToMyth.full_to_pretty_myth_string ~problem invariant)));
          let overstrong_model =
            check_boundary
              ~problem
              ~invariant
              ~positives:(TestBed.positives ~testbed)
          in
          begin match overstrong_model with
            | [] ->
              let model = ces in
              let model =
                begin match model with
                  | [] ->
                    let model =
                      verify_proves_post
                        ~problem
                        ~invariant
                        ~post
                    in
                    let model =List.filter
                      ~f:(fun n -> not (TestBed.contains_test ~testbed n))
                      model
                    in
                    Log.info (lazy ("postcondition unproven, counterexample: "
                                    ^ (List.to_string ~f:Value.show model)));
                    model
                  | _ ->
                    Log.info (lazy ("Prior counterexample: " ^ (List.to_string ~f:Value.show model)));
                    model
                end
              in
              let model =
                begin match model with
                  | [] ->
                    if Expr.equal invariant (Expr.mk_constant_true_func Type._t) then
                      []
                    else
                      let model = verify_module ~problem ~invariant in
                      List.filter
                        ~f:(fun n -> not (TestBed.contains_test ~testbed n))
                        model
                  | _ -> model
                end
              in
              begin match model with
                | [] -> invariant
                | _ ->
                  let testbed =
                    TestBed.add_neg_tests
                      ~testbed
                      model
                  in
                  let new_inv =
                    synth_new_inv
                      ~problem
                      ~testbed
                  in
                  let answer_lists = (new_inv,testbed,[])::(old_invariant,old_testbed,model)::answer_lists in
                  learnVPreCondTrueAllInternal
                    ~answer_lists
              end
            | new_positives ->
              let answer_lists =
                valid_answer_lists
                  ~problem
                  ~answer_lists
                  ~new_positives
              in
              learnVPreCondTrueAllInternal
                ~answer_lists
          end
      end
    in
    let true_invariant = Expr.mk_constant_true_func Type._t in
    let false_invariant = Expr.mk_constant_false_func Type._t in
    let testbed = TestBed.create_positive [] in
    let answer_lists = [(false_invariant,testbed,[]);(true_invariant,testbed,[])] in
    learnVPreCondTrueAllInternal
      ~answer_lists


  let learnVPreCondAll
      ~(problem : Problem.t)
      ~(pre : Expr.t)
      ~(post : Value.t LR.condition)
      ~(positives : Value.t list)
      ~(checker : Expr.t -> (Value.t list) * (Value.t list))
    : (Expr.t,(Value.t list) * (Value.t list)) Either.t =
    let rec helper
        (attempt:int)
        (testbed:TestBed.t)
        (pres:Expr.t list)
      : (Expr.t,Value.t list * Value.t list) Either.t =
      (Log.info (lazy ("VPIE Attempt "
                       ^ (Int.to_string attempt)
                       ^ "."));
       let pres =
         begin match List.filter ~f:(satisfies_testbed ~problem testbed) pres with
           | [] ->
             let subvalues =
               List.concat_map
                 ~f:Value.strict_subvalues
                 (testbed.pos_tests@testbed.neg_tests)
             in
             let all_inside_examples =
               List.filter
                 ~f:(fun e ->
                     Typecheck.type_equiv
                       problem.tc
                       (Type._t)
                       (Typecheck.typecheck_exp problem.ec problem.tc problem.vc (Value.to_exp e)))
                 subvalues
             in
             let testbed =
               List.fold_left
                 ~f:(fun tb e ->
                     if not
                         (List.is_empty
                            (snd
                               (L.verifier
                                  ~problem
                                  (Type.mk_arrow (Type._t) (Type._t))
                                  post
                                  (LR.Set [e])
                                  (Value.from_exp_exn (Expr.mk_identity_func Type._t))))) then
                       TestBed.add_neg_test ~testbed:tb e
                     else
                       (if TestBed.contains_test ~testbed:tb e then
                          tb
                        else
                          TestBed.add_pos_test ~testbed:tb e))
                 ~init:testbed
                 all_inside_examples
             in
             Log.info (lazy "testbed");
             Log.info (lazy (TestBed.show testbed));
             List.map ~f:(fun e -> assert (satisfies_testbed ~problem testbed e); Expr.simplify e) (snd (S.synth ~problem ~testbed:testbed))
           | pres ->
             pres
         end
       in
       let synthed_pre = List.hd_exn pres in
       Log.info (lazy ("Candidate Precondition: " ^ (DSToMyth.full_to_pretty_myth_string ~problem synthed_pre)));
       let full_pre = Expr.and_predicates pre synthed_pre in
       let boundary_ce =
         checker full_pre
       in
       begin match boundary_ce with
         | ([],[]) ->
           let model_o =
             List.fold_left
               ~f:(fun acc (eval,eval_t) ->
                   begin match acc with
                     | [] ->
                       Log.info (lazy ("verifying: " ^ DSToMyth.full_to_pretty_myth_string ~problem eval));
                       fst
                       (L.verifier
                         ~problem
                         eval_t
                         post
                         (LR.Predicate
                            (fun v ->
                               Value.equal
                                 Value.mk_true
                                 (Eval.evaluate_with_holes_basic
                                         ~tc:problem.tc
                                    ~eval_context:problem.eval_context
                                    (Expr.mk_app
                                       full_pre
                                       (Value.to_exp v)))))
                         (Eval.evaluate_with_holes_basic ~tc:problem.tc ~eval_context:problem.eval_context eval))
                       (*V.implication_counter_example
                         ~problem
                         ~pre:full_pre
                         ~eval
                         ~eval_t
                         ~post*)
                     | _ -> acc
                   end)
               ~init:[]
               problem.mod_vals
           in
           begin match model_o with
             | [] ->
               Log.info (lazy ("Verified Precondition: " ^ (DSToMyth.full_to_pretty_myth_string ~problem synthed_pre)));
               First synthed_pre
             | model ->
               let new_negs =
                 List.filter
                   ~f:(fun n -> not (TestBed.contains_test ~testbed n))
                   model
               in
               assert (List.length new_negs > 0);
                 Log.info (lazy ("Add negative examples: " ^ (List.to_string ~f:Value.show model)));
                 helper
                   (attempt+1)
                   (TestBed.add_neg_tests
                      ~testbed
                      new_negs)
                   pres
           end
         | ce -> Second ce
       end)
    in
    let testbed = TestBed.create_positive positives in
    helper 0 testbed [Expr.mk_constant_true_func (Type._t)]

  let learnVPreCond
      ~(problem:Problem.t)
      ~(pre:Expr.t)
      ~(eval : Expr.t)
      ~(eval_t : Type.t)
      ~(post : UniversalFormula.t)
      ~(positives : Value.t list)
    : Expr.t =
    let rec helper
        (attempt:int)
        (testbed:TestBed.t)
      : Expr.t =
       let pres =
         begin match List.filter ~f:(satisfies_testbed ~problem testbed) !possibilities with
           | [] ->
             (Log.info (lazy ("Learning new precondition set.")));
             let subvalues =
               List.concat_map
                 ~f:Value.strict_subvalues
                 (testbed.pos_tests@testbed.neg_tests)
             in
             let all_inside_examples =
               List.filter
                 ~f:(fun e ->
                     Typecheck.type_equiv
                       problem.tc
                       (Type._t)
                       (Typecheck.typecheck_exp problem.ec problem.tc problem.vc (Value.to_exp e)))
                 subvalues
             in
             let testbed =
               List.fold_left
                 ~f:(fun tb e ->
                     if not
                         (List.is_empty
                            (V.true_on_examples
                               ~problem
                               ~examples:[e]
                               ~eval:(Expr.mk_identity_func (Type._t))
                               ~eval_t:(Type.mk_arrow (Type._t) (Type._t))
                               ~post:post)) then
                       TestBed.add_neg_test ~testbed:tb e
                     else
                       TestBed.add_pos_test ~testbed:tb e
                   )
                 ~init:testbed
                 all_inside_examples
             in
             Log.info (lazy "testbed");
             Log.info (lazy (TestBed.show testbed));
             let pres = List.map ~f:Expr.simplify (snd (S.synth ~problem ~testbed:testbed))
              in possibilities := pres
               ; pres
           | pres ->
             pres
         end
       in
      (Log.info (lazy ("VPIE Attempt "
                       ^ (Int.to_string attempt)
                       ^ "."));
       let synthed_pre = List.hd_exn pres in
       Log.info (lazy ("Candidate Precondition: " ^ (DSToMyth.full_to_pretty_myth_string ~problem synthed_pre)));
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
         | [] ->
           Log.info (lazy ("Verified Precondition: " ^ (DSToMyth.full_to_pretty_myth_string ~problem synthed_pre)));
           synthed_pre
         | model ->
           if (List.length model <> 1) then
             failwith ("cannot do such functions yet: " ^ (List.to_string ~f:Value.show model))
           else
             let new_neg_example = List.hd_exn model in
             (*negs := new_neg_example::!negs;*)
             Log.info (lazy ("Add negative example: " ^ (Value.show new_neg_example)));
             helper
               (attempt+1)
               (TestBed.add_neg_test ~testbed new_neg_example)
       end)
    in
    let testbed = TestBed.create_positive positives in
    let testbed =
      List.fold
        ~f:(fun testbed n -> TestBed.add_neg_test ~testbed n)
        ~init:testbed
        !negs
    in
    helper 0 testbed
end
