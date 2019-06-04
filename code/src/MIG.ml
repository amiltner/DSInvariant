open Core

open Lang

module MIGLearner(V : Verifier.t) (S : Synthesizer.t) = struct
  module VPIE = VPIE.Make(V)(S)

  let push_boundary
      ~(problem : problem)
      ~eval:(eval : Expr.t)
      ~(eval_t : Type.t)
      ~post:(post : UniversalFormula.t)
      ~positives:(positives : Value.t list)
    : Value.t option =
    Log.info
      (lazy ("Checking boundary for: " ^ Expr.show eval));
    Option.map
      ~f:(List.hd_exn)
      (V.true_on_examples
         ~problem
         ~examples:positives
         ~eval
         ~eval_t
         ~post)

  let satisfyTransAll
      ~problem:(problem : problem)
      ~invariant:(invariant : Expr.t)
      ~positives:(positives : Value.t list)
    : ((Expr.t,Value.t) Either.t) =
    let rec helper
        (invariant : Expr.t)
      : ((Expr.t,Value.t) Either.t) =
      let app_var = "x" in
      let invariant_applied = Expr.mk_app invariant (Expr.mk_var app_var) in
      let applied_arg = (app_var, Type.mk_var "t") in
      let post = ([applied_arg],invariant_applied) in
      let boundary_validity =
        List.fold_left
          ~f:(fun acc (eval,eval_t) ->
              begin match acc with
                | None ->
                  push_boundary
                    ~problem
                    ~eval
                    ~eval_t
                    ~post
                    ~positives
                | Some _ -> acc
              end)
          ~init:None
          problem.mod_vals
      in
      begin match boundary_validity with
        | Some m ->
          Log.info
            (lazy ("Boundary Not Satisfied, counterexample:"
                   ^ (Log.indented_sep 4)
                   ^ (Value.show m))) ;
          Second m
        | None ->
          Log.info
            (lazy ("IND >> Strengthening for inductiveness:"
                   ^ (Log.indented_sep 4)
                   ^ (Expr.show invariant))) ;
          let pre_inv =
            VPIE.learnVPreCondAll
              ~problem
              ~pre:invariant
              ~post
              ~positives:positives
          in
          Log.debug (lazy ("IND Delta: " ^ (Expr.show pre_inv))) ;
          if Expr.equal pre_inv (Expr.mk_constant_true_func Type.mk_t_var) then
            First (Expr.and_predicates pre_inv invariant)
          else
            helper pre_inv
      end
    in
    helper invariant

  let satisfyTrans
      ~problem:(problem : problem)
      ~invariant:(invariant : Expr.t)
      ~eval:(eval : Expr.t)
      ~eval_t:(eval_t : Type.t)
      ~positives:(positives : Value.t list)
    : ((Expr.t,Value.t) Either.t) =
    Log.info
      (lazy ("Checking Satisfy Transitivity for: " ^ Expr.show eval));
    let rec helper
        (invariant : Expr.t)
      : ((Expr.t,Value.t) Either.t) =
      let app_var = "x" in
      let invariant_applied = Expr.mk_app invariant (Expr.mk_var app_var) in
      let applied_arg = (app_var, Type.mk_var "t") in
      let post = ([applied_arg],invariant_applied) in
      let boundary_validity =
        push_boundary
          ~problem
          ~eval
          ~eval_t
          ~post
          ~positives
      in
      begin match boundary_validity with
        | Some m ->
          Log.info
            (lazy ("Boundary Not Satisfied, counterexample:"
                   ^ (Log.indented_sep 4)
                   ^ (Value.show m))) ;
          Second m
        | None ->
          Log.info
            (lazy ("IND >> Strengthening for inductiveness:"
                   ^ (Log.indented_sep 4)
                   ^ (Expr.show invariant))) ;
          let pre_inv =
            VPIE.learnVPreCond
              ~problem
              ~pre:invariant
              ~eval
              ~eval_t
              ~post
              ~positives:positives
          in
          Log.debug (lazy ("IND Delta: " ^ (Expr.show pre_inv))) ;
          if Expr.equal pre_inv invariant then
            First invariant
          else
            let new_inv = Expr.and_predicates pre_inv invariant in
            helper new_inv
      end
    in
    helper invariant

  let rec learnInvariant_internal
      ~problem:(problem : problem)
      ~positives:(positives : Value.t list)
      ~attempt:(attempt:int)
    : Expr.t =
    let restart_with_new_positives
        (positive : Value.t)
      : Expr.t =
      begin
        Log.warn (lazy ("Restarting inference engine. Attempt was "
                        ^ (string_of_int attempt)
                        ^ ".")) ;
        learnInvariant_internal
          ~problem
          ~positives:(positive::positives)
          ~attempt:(attempt+1)
      end
    in
    (* find I => Q *)
    let initial_invariant =
      VPIE.learnVPreCond
        ~problem
        ~pre:(Expr.mk_constant_true_func problem.module_type)
        ~eval:(Expr.mk_identity_func (Type.mk_var "t"))
        ~eval_t:(Type.mk_arr (Type.mk_var "t") (Type.mk_var "t"))
        ~post:problem.post
        ~positives:positives
    in
    (* inductiveness checks and updates to invariants *)
    (* terminates when either all have been processed and found invariant *)
    (* or until it becomes too strong, and a positive counterexample is added *)
    let inv_or_pos =
      satisfyTransAll
        ~problem
        ~invariant:initial_invariant
        ~positives
    in
    (*let inv_or_pos =
      fold_until_right_or_list_end
        ~f:(fun acc (e,t) ->
            satisfyTrans
              ~problem
              ~invariant:acc
              ~eval:e
              ~eval_t:t
              ~positives)
        ~init:initial_invariant
        problem.mod_vals
      in*)
    begin match inv_or_pos with
      | First inv -> inv
      | Second ce -> restart_with_new_positives ce
    end

  let learnInvariant
      ~unprocessed_problem:(unprocessed_problem : unprocessed_problem)
    : string =
    let problem = ProcessFile.process_full_problem unprocessed_problem in
    let (a,modi,c,d,e) = problem.unprocessed in
    let inv =
       learnInvariant_internal
         ~problem
         ~positives:[]
         ~attempt:0
    in
    let full_ret =
      match problem.accumulator with
      | None -> Type.mk_bool_var
      | Some acc -> Type.mk_tuple [Type.mk_bool_var;acc]
    in
    let t' = get_foldable_t problem.tc full_ret in
    let modi = modi@[Declaration.TypeDeclaration (Id.mk_prime "t", t')] in
    let problem' = { problem with
                     unprocessed = (a,modi,c,d,e) }
    in
    DSToMyth.to_pretty_myth_string
      ~problem:problem'
      inv
end
