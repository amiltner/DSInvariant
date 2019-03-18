open MyStdlib
open Utils
open Verifiers
open SetSimulator

module MIGLearner(V : Verifier) = struct
  module VPIE = VPIE.Make(V)
  module SetSimulator = SetSimulatorImpl(V)

  let push_boundary
      ~(sygus : V.expr SyGuS_Set.t)
      ~(code : V.expr)
      ~(postcondition : V.expr)
      ~(states : Value.t list list)
    : model option =
    let testbed =
      TestBed.create_positive
        states
        ~args:sygus.synth_variables
        ~post:(fun _ res ->
            match res with
            | Ok v when v = Value.Bool false -> true
            | _ -> false)
    in
    SetSimulator.check_condition_held_after_evals
      ~testbed
      ~code
      ~condition:postcondition


  let satisfyTrans
      ~pre_expr:(_ : V.expr)
      ~(invariant : V.expr)
      ~(code : V.expr)
      ~(sygus : V.expr SyGuS_Set.t)
      ~(states : Value.t list list)
    : (V.expr * model option) =
    let rec helper (invariant : V.expr) : (V.expr * model option) =
      let boundary_validity =
        push_boundary
          ~sygus
          ~code
          ~postcondition:invariant
          ~states
      in
      begin match boundary_validity with
        | Some m ->
          Log.info
            (lazy ("Boundary Not Satisfied, counterexample:"
                   ^ (Log.indented_sep 4)
                   ^ (string_of_list (string_of_pair ident Value.to_string) m))) ;

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
                          states
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
    helper invariant

  let learnSetInvariant_internal
      ~(states : Value.t list list)
      ~(sygus : V.expr SyGuS_Set.t)
    : V.expr =
    let rec learnSetInvariant_internal
        ~(states : Value.t list list)
        ~(attempt:int)
      : V.expr =
      let open Quickcheck in
      let open SetSimulator in
      let restart_with_new_states
          (head : Value.t list)
        : V.expr =
          begin
            Log.warn (lazy ("Restarting inference engine. Attempt "
                            ^ (string_of_int attempt)
                            ^ ".")) ;
            learnSetInvariant_internal
              ~attempt:attempt
              ~states:(List.dedup_and_sort ~compare:(compare Value.compare) (head::states))
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
          ~testbed:(TestBed.create_positive states
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
                ~states
                ~code:inserted_xy
                ~invariant with
        | inv, None ->
          V.simplify inv
        | _, (Some ce_model) ->
          restart_with_new_states
            (Option.value_exn (random_value
                                 (gen_state_from_model sygus (Some ce_model))))
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
                ~states
                ~code:deleted_xy
                ~invariant with
        | inv, None ->
          V.simplify inv
          (*restart_with_new_states
            (random_value
               ~seed:(`Deterministic seed_string)
               (gen_pre_state
                  ~verifier:(module V)
                  ~use_trans:true
                  sygus))*)
        | _, (Some ce_model) ->
          restart_with_new_states
            (Option.value_exn (random_value
                                 (gen_state_from_model sygus (Some ce_model))))
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
        restart_with_new_states
          (Option.value_exn (random_value
                               (gen_state_from_model sygus (Some ce_model))))
      end
    in
    learnSetInvariant_internal
      ~states
      ~attempt:1

  (*let make_sygus_verifier_state
      (type t)
      ~verifier:(module V : Verifier with type t = t)
      ~(sygus : SyGuS_Set.t)
    : V.t =
    let verifier_state = V.empty in
    let verifier_state = V.register_func verifier_state sygus.insert_func in
    let verifier_state = V.register_func verifier_state sygus.delete_func in
    let verifier_state = V.register_func verifier_state sygus.lookup_func in
    let verifier_state = V.register_func verifier_state sygus.post_func in
    verifier_state*)



  let learnSetInvariant
      (*?(conf = default_config)*)
        ~states:(states : Value.t list list)
        (sygus : V.expr SyGuS_Set.t)
    : Job.desc =
    let ans = V.to_string
      (learnSetInvariant_internal
         ~states
         ~sygus)
    in
    ans
end
