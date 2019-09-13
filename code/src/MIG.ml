open Core

module Make
    (V : Verifier.t)
    (S : Synthesizer.t)
    (L : LR.t)
  = struct
  module VPIE = VPIE.Make(V)(S)

  let push_boundary
      ~(problem : Problem.t)
      ~eval:(eval : Expr.t)
      ~(eval_t : Type.t)
      ~post:(post : UniversalFormula.t)
      ~positives:(positives : Value.t list)
    : Value.t list =
    Log.info
      (lazy ("Checking boundary for:" ^ (DSToMyth.full_to_pretty_myth_string ~problem eval)));
      (V.true_on_examples
         ~problem
         ~examples:positives
         ~eval
         ~eval_t
         ~post)

  let satisfyTransAll
      ~problem:(problem : Problem.t)
      ~invariant:(invariant : Expr.t)
      ~positives:(positives : Value.t list)
    : ((Expr.t,Value.t list) Either.t) =
    let create_invariant_post
        (invariant:Expr.t)
      : UniversalFormula.t =
      let app_var = "x" in
      let invariant_applied = Expr.mk_app invariant (Expr.mk_var app_var) in
      let applied_arg = (app_var, Type._t) in
      ([applied_arg],invariant_applied)
    in
    let check_boundary
        (invariant:Expr.t)
      : Value.t list =
      let post = create_invariant_post invariant in
      List.fold_left
        ~f:(fun acc (eval,eval_t) ->
            begin match acc with
              | [] ->
                push_boundary
                  ~problem
                  ~eval
                  ~eval_t
                  ~post
                  ~positives
              | _ -> acc
            end)
        ~init:[]
        problem.mod_vals
    in
    let rec helper
        (invariant : Expr.t)
      : ((Expr.t,Value.t list) Either.t) =
      let post = create_invariant_post invariant in
      let pre_or_ce =
        VPIE.learnVPreCondAll
          ~problem
          ~pre:invariant
          ~post
          ~positives:positives
          ~checker:check_boundary
      in
      Log.info
        (lazy ("IND >> Strengthening for inductiveness:"
               ^ (Log.indented_sep 4)
               ^ (DSToMyth.full_to_pretty_myth_string ~problem invariant))) ;
      begin match pre_or_ce with
        | First pre_inv ->
          Log.debug (lazy ("IND Delta: " ^ (DSToMyth.full_to_pretty_myth_string ~problem  pre_inv))) ;
          if Expr.equal pre_inv (Expr.mk_constant_true_func (Type._t)) then
            First (Expr.and_predicates pre_inv invariant)
          else
            helper pre_inv
        | Second m ->
          Log.info
            (lazy ("Boundary Not Satisfied, counterexample:"
                   ^ (Log.indented_sep 4)
                   ^ (List.to_string ~f:Value.show m))) ;
          Second m
      end
    in
    helper invariant

  let satisfyTrans
      ~problem:(problem : Problem.t)
      ~invariant:(invariant : Expr.t)
      ~eval:(eval : Expr.t)
      ~eval_t:(eval_t : Type.t)
      ~positives:(positives : Value.t list)
    : ((Expr.t,Value.t list) Either.t) =
    Log.info
      (lazy ("Checking Satisfy Transitivity for: " ^ (DSToMyth.full_to_pretty_myth_string ~problem eval)));
    let rec helper
        (invariant : Expr.t)
      : ((Expr.t,Value.t list) Either.t) =
      let app_var = "x" in
      let invariant_applied = Expr.mk_app invariant (Expr.mk_var app_var) in
      let applied_arg = (app_var, Type._t) in
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
        | [] ->
          Log.info
            (lazy ("IND >> Strengthening for inductiveness:"
                   ^ (Log.indented_sep 4)
                   ^ (DSToMyth.full_to_pretty_myth_string ~problem invariant))) ;
          let pre_inv =
            VPIE.learnVPreCond
              ~problem
              ~pre:invariant
              ~eval
              ~eval_t
              ~post
              ~positives:positives
          in
          Log.debug (lazy ("IND Delta: " ^ (DSToMyth.full_to_pretty_myth_string ~problem pre_inv))) ;
          if Expr.equal pre_inv invariant then
            First invariant
          else
            let new_inv = Expr.and_predicates pre_inv invariant in
            helper new_inv
        | m ->
          Log.info
            (lazy ("Boundary Not Satisfied, counterexample:"
                   ^ (Log.indented_sep 4)
                   ^ (List.to_string ~f:Value.show m))) ;
          Second m
      end
    in
    helper invariant

  let rec learnInvariant_internal
      ~(problem : Problem.t)
      ~(positives : Value.t list)
      ~(attempt:int)
    : Expr.t =
    let restart_with_new_positives
        (positive : Value.t list)
      : Expr.t =
      begin
        Log.warn (lazy ("Restarting inference engine. Attempt was "
                        ^ (string_of_int attempt)
                        ^ ".")) ;
        learnInvariant_internal
          ~problem
          ~positives:(positive@positives)
          ~attempt:(attempt+1)
      end
    in
    (* find I => Q *)
    let initial_invariant =
      VPIE.learnVPreCond
        ~problem
        ~pre:(Expr.mk_constant_true_func problem.module_type)
        ~eval:(Expr.mk_identity_func (Type._t))
        ~eval_t:(Type.mk_arrow (Type._t) (Type._t))
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
    match inv_or_pos with
    | First inv -> inv
    | Second ce -> restart_with_new_positives ce

  let learnInvariant ~(unprocessed_problem : Problem.t_unprocessed)
                     : string =
    let problem = Problem.process unprocessed_problem in
    let inv = learnInvariant_internal
        ~problem
                ~positives:[]
                ~attempt:0
    in
    DSToMyth.full_to_pretty_myth_string inv
      ~problem
end
