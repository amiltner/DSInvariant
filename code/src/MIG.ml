open MyStdlib
open Verifiers
open Lang

module MIGLearner(V : Verifier) = struct
  module VPIE = VPIE.Make(V)

  let push_boundary
      ~sygus:(_ : Expr.t Problem.t)
      ~code:(_ : Expr.t)
      ~postcondition:(_ : Expr.t)
      ~positives:(_ : Value.t list)
    : Expr.t option =
    (*let _ =
      TestBed.create_positive
        (List.map ~f:(fun x -> [x]) positives)
        ~args:sygus.synth_variables
        ~post:(fun _ res ->
            match res with
            | Ok v when v = Value.Bool false -> true
            | _ -> false)
      in*)
    failwith "TODO"
    (*SetSimulator.check_condition_held_after_evals
      ~testbed
      ~code
      ~condition:postcondition*)


  let satisfyTrans
      ~pre_expr:(_ : Expr.t)
      ~invariant:(_ : Expr.t)
      ~code:(_ : Expr.t)
      ~sygus:(_ : Expr.t Problem.t)
      ~positives:(_ : Value.t list)
    : (Expr.t * Expr.t option) =
    (*let rec helper (invariant : Expr.t) : (V.expr * V.expr option) =
      let boundary_validity =
        push_boundary
          ~sygus
          ~code
          ~postcondition:invariant
          ~positives
      in
      begin match boundary_validity with
        | Some m ->
          (*Log.info
            (lazy ("Boundary Not Satisfied, counterexample:"
                   ^ (Log.indented_sep 4)
                   ^ (string_of_list (string_of_pair ident Value.to_string) m))) ;*)

          (V.true_exp,Some m)
        | None ->
          let invf_call = invariant in
          let invf'_call =
            V.substitute
              invariant
              [V.integer_var_exp "x";V.integer_var_exp "y"]
              [V.integer_var_exp "x!";V.integer_var_exp "y!"]
          in
          let eval =
              code
          in
          Log.info
            (lazy ("IND >> Strengthening for inductiveness:"
                   ^ (Log.indented_sep 4)
                   ^ (V.to_string invariant))) ;
          let pre_inv =
            VPIE.learnVPreCond
              ~pre:invf_call
              ~eval
              ~consts:sygus.constants
              ~post:invf'_call
              ~testbed:(TestBed.create_positive
                          (List.map ~f:(fun x -> [x]) positives)
                          ~args:sygus.synth_variables
                          ~post:(fun _ res ->
                              match res with
                              | Ok v when v = Value.Bool false -> true
                              | _ -> false))
          in
          Log.debug (lazy ("IND Delta: " ^ (V.to_string pre_inv))) ;
          if V.equal pre_inv V.true_exp || V.equal pre_inv V.alternative_true_exp then
            (invariant, None)
          else
            let new_inv = V.bin_and_exps pre_inv invariant in
            helper new_inv
      end
    in
      helper invariant*)
    failwith "ah"

  let learnSetInvariant_internal
      ~positives:(_ : Value.t list)
      ~sygus:(_ : Expr.t Problem.t)
    : Expr.t =
    (*let rec learnSetInvariant_internal
        ~(positives : Value.t list)
        ~(attempt:int)
      : Expr.t =
      let restart_with_new_positives
          (positive : Value.t)
        : Expr.t =
          begin
            Log.warn (lazy ("Restarting inference engine. Attempt "
                            ^ (string_of_int attempt)
                            ^ ".")) ;
            learnSetInvariant_internal
              ~attempt:attempt
              ~positives:(List.dedup_and_sort ~compare:Value.compare (positive::positives))
          end
      in
      (* I => Q *)
      let post_expr =
        sygus.post_func
          ~verifier:(module V)
          (V.make_pair
             (V.integer_var_exp "x")
             (V.integer_var_exp "y"))
          (V.integer_var_exp "z")
      in
      let pre_expr =
        sygus.precond_func
          ~verifier:(module V)
          (V.make_pair
             (V.integer_var_exp "x")
             (V.integer_var_exp "y"))
          (V.integer_var_exp "z")
      in
      let invariant =
        VPIE.learnVPreCond
          ~pre:V.true_exp
          ~eval:pre_expr
          ~post:post_expr
          ~consts:sygus.constants
          ~testbed:(TestBed.create_positive
                      (List.map ~f:(fun x -> [x]) positives)
                      ~args:sygus.synth_variables
                      ~post:(fun _ res ->
                          match res with
                          | Ok v when v = Value.Bool false -> true
                          | _ -> false))
      in
      (* {I'} s = insert y s {I} *)
      let inserted_xy =
        sygus.insert_func
          ~verifier:(module V)
          (V.make_pair
             (V.integer_var_exp "x")
             (V.integer_var_exp "y"))
          (V.integer_var_exp "z")
      in
      (*let set_xyprime_to_inserted =
        V.bin_and_exps
          (V.mk_equals (V.integer_var_exp "x!") (V.get_fst inserted_xy))
          (V.mk_equals (V.integer_var_exp "y!") (V.get_snd inserted_xy))
        in*)
      let invariant =
        match satisfyTrans
                ~pre_expr
                ~sygus
                ~positives
                ~code:inserted_xy
                ~invariant with
        | inv, None ->
          V.simplify inv
        | _, (Some ce_model) ->
          restart_with_new_positives
            (V.to_value_exn ce_model)
      in
      (* {I'} s = delete y s {I} *)
      let deleted_xy =
        sygus.delete_func
          ~verifier:(module V)
          (V.make_pair
             (V.integer_var_exp "x")
             (V.integer_var_exp "y"))
          (V.integer_var_exp "z")
      in
      (*let set_xyprime_to_deleted =
        V.bin_and_exps
          (V.mk_equals (V.integer_var_exp "x!") (V.get_fst deleted_xy))
          (V.mk_equals (V.integer_var_exp "y!") (V.get_snd deleted_xy))
        in*)
      let invariant =
        match satisfyTrans
                ~pre_expr
                ~sygus
                ~positives
                ~code:deleted_xy
                ~invariant with
        | inv, None ->
          V.simplify inv
        (*restart_with_new_positives
            (random_value
               ~seed:(`Deterministic seed_string)
               (gen_pre_state
                  ~verifier:(module V)
                  ~use_trans:true
                  sygus))*)
        | _, (Some ce_model) ->
          ce_model
      in
      let empty =
        sygus.empty_func
          ~verifier:(module V)
          (V.make_pair
             (V.integer_var_exp "x")
             (V.integer_var_exp "y"))
          (V.integer_var_exp "z")
      in
      begin match V.implication_counter_example
                    ~resultant:false
                    ~pre:(V.bin_and_exps V.true_exp empty)
                    ~eval:(pre_expr) (*TODO: confirm this works *)
                    ~post:invariant
        None with
      | None -> invariant
      | Some ce_model ->
        V.from_value @$ List.hd_exn ce_model
      end
    in
    learnSetInvariant_internal
      ~positives
      ~attempt:1*)
    failwith "ah"

  (*let make_sygus_verifier_state
      (type t)
      ~verifier:(module V : Verifier with type t = t)
      ~(sygus : Problem.t)
    : V.t =
    let verifier_state = V.empty in
    let verifier_state = V.register_func verifier_state sygus.insert_func in
    let verifier_state = V.register_func verifier_state sygus.delete_func in
    let verifier_state = V.register_func verifier_state sygus.lookup_func in
    let verifier_state = V.register_func verifier_state sygus.post_func in
    verifier_state*)



  let learnSetInvariant
      (*?(conf = default_config)*)
      ~positives:(positives : Value.t list)
        (sygus : Expr.t Problem.t)
    : Job.desc =
    let ans = Expr.show
      (learnSetInvariant_internal
         ~positives
         ~sygus)
    in
    ans
end
