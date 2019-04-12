open MyStdlib
open Verifiers
open Lang

module MIGLearner(V : Verifier) = struct
  module VPIE = VPIE.Make(V)

  let push_boundary
      ~(problem : problem)
      ~eval:(eval : Expr.t)
      ~post:(post : UniversalFormula.t)
      ~positives:(positives : Value.t list)
    : Value.t option =
    V.true_on_examples
      ~problem
      ~examples:positives
      ~eval
      ~post

  let satisfyTrans
      ~problem:(problem : problem)
      ~invariant:(invariant : Expr.t)
      ~eval:(eval : Expr.t)
      ~positives:(positives : Value.t list)
    : ((Expr.t,Value.t) either) =
    Log.info
      (lazy ("Checking Satisfy Transitivity for: " ^ Expr.show eval));
    let rec helper
        (invariant : Expr.t)
      : ((Expr.t,Value.t) either) =
      print_endline @$ Expr.show invariant;
      let (arg,invariant_internal) =
        Expr.destruct_func_exn
          invariant
      in
      let post = ([arg],invariant_internal) in
      let boundary_validity =
        push_boundary
          ~problem
          ~eval
          ~post
          ~positives
      in
      begin match boundary_validity with
        | Some m ->
          Log.info
            (lazy ("Boundary Not Satisfied, counterexample:"
                   ^ (Log.indented_sep 4)
                   ^ (Value.show m))) ;
          Right m
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
              ~post
              ~positives:positives
          in
          Log.debug (lazy ("IND Delta: " ^ (Expr.show pre_inv))) ;
          if is_equal @$ Expr.compare pre_inv invariant then
            Left invariant
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
        Log.warn (lazy ("Restarting inference engine. Attempt "
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
        ~post:problem.post
        ~positives:positives
    in
    (* inductiveness checks and updates to invariants *)
    (* terminates when either all have been processed and found invariant *)
    (* or until it becomes too strong, and a positive counterexample is added *)
    let inv_or_pos =
      fold_until_right_or_list_end
        ~f:(fun acc e ->
            satisfyTrans
              ~problem
              ~invariant:acc
              ~eval:e
              ~positives)
        ~init:initial_invariant
        problem.mod_vals
    in
    begin match inv_or_pos with
      | Left inv -> inv
      | Right ce -> restart_with_new_positives ce
    end

  let learnInvariant
      ~unprocessed_problem:(unprocessed_problem : unprocessed_problem)
    : string =
    let problem = ProcessFile.process_full_problem unprocessed_problem in
    Expr.show
      (learnInvariant_internal
         ~problem
         ~positives:[]
         ~attempt:0)
end
