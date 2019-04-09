open MyStdlib
open Utils
open SetVPie
open SetVerifiers
open SetSimulator

module SIGLearner(V : Verifier) = struct
  module SetVPie = SetVPieImpl(V)
  module SetSimulator = SetSimulatorImpl(V)

  type 'a config = {
    for_VPIE : 'a SetVPie.config ;

    base_random_seed : string ;
    max_restarts : int ;
    max_steps_on_restart : int ;
    model_completion_mode : [ `RandomGeneration | `UsingZ3 ] ;
    verifier : [ `QuickCheck | `Z3 ] ;
  }

  let default_config = {
    for_VPIE = {
      SetVPie.default_config with simplify = false ;
    } ;

    base_random_seed = "SetInvGen" ;
    max_restarts = 64 ;
    max_steps_on_restart = 256 ;
    model_completion_mode = `RandomGeneration ;
    verifier = `Z3 ;
  }

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
      ~(conf : Value.t list config)
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
            SetVPie.learnVPreCond
              ~pre:invf_call
              ~conf:conf.for_VPIE
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
      ~(conf : Value.t list config)
      ~(restarts_left : int)
      ~(states : Value.t list list)
      ~(sygus : V.expr SyGuS_Set.t)
      ~(seed_string : string)
    : V.expr =
    let rec learnSetInvariant_internal
        ~(restarts_left : int)
        ~(states : Value.t list list)
        ~(seed_string : string)
      : V.expr =
      let open Quickcheck in
      let open SetSimulator in
      let restart_with_new_states
          (head : Value.t list option)
        : V.expr =
        if restarts_left < 1 then
          (Log.error
             (lazy
               ("Reached MAX ("
                ^ (string_of_int conf.max_restarts)
                ^ ") restarts. Giving up ..."));
           V.false_exp)
        else
          begin
            Log.warn (lazy ("Restarting inference engine. Attempt "
                            ^ (string_of_int (1 + conf.max_restarts - restarts_left))
                            ^ "/" ^ (string_of_int conf.max_restarts) ^".")) ;
            learnSetInvariant_internal
              ~restarts_left:(restarts_left - 1) 
              ~states:List.(dedup_and_sort ~compare:(compare Value.compare) (
                  states @ (random_value ~size:conf.max_steps_on_restart ~seed:(`Deterministic seed_string)
                              (simulate_from sygus head))))
              ~seed_string:(seed_string ^ "#")
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
        SetVPie.learnVPreCond
          ~pre:V.true_exp
          ~conf:conf.for_VPIE
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
                ~conf
                ~sygus
                ~states
                ~code:inserted_xy
                ~invariant with
        | inv, None ->
          V.simplify inv
        | _, (Some ce_model) ->
          restart_with_new_states
            (random_value
               ~seed:(`Deterministic seed_string)
               (gen_state_from_model sygus (Some ce_model)))
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
                ~conf
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
            (random_value
               ~seed:(`Deterministic seed_string)
               (gen_state_from_model sygus (Some ce_model)))
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
          (random_value
             ~seed:(`Deterministic seed_string)
             (gen_state_from_model sygus (Some ce_model)))
      end
    in
    learnSetInvariant_internal
      ~restarts_left
      ~states
      ~seed_string

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
         ~conf:default_config
         ~restarts_left:default_config.max_restarts
         ~states
         ~sygus
         ~seed_string:default_config.base_random_seed)
    in
      ans


  (*let intlist_generator =
    Quickcheck.Generator.list Quickcheck.Generator.small_non_negative_int
  in
  let intlist_seq =
    Sequence.filter
      ~f:(fun l -> List.length l < 5)
      (Quickcheck.random_sequence intlist_generator)
  in
  let intlist_list = Sequence.to_list (Sequence.take intlist_seq 80)
  in
  let rec sublists = function
    | []    -> [[]]
    | x::xs -> let ls = sublists xs in
      (x::xs)::ls
  in
  let all_inside_examples =
    List.concat_map
      ~f:sublists
      intlist_list
  in
  let testbed =
    List.fold_left
      ~f:(fun tb l ->
          if Option.is_some (SetSimulator.check_condition_held_after_eval
                               ~test:[("x",Type.INTLIST, IntList l)]
                               ~code:(sygus.precond_func
                                        ~verifier:(module V)
                                        (V.make_pair
                                           (V.integer_var_exp "x")
                                           (V.integer_var_exp "y"))
                                        (V.integer_var_exp "z"))
                               ~condition:(sygus.post_func
                                             ~verifier:(module V)
                                             (V.make_pair
                                                (V.integer_var_exp "x")
                                                (V.integer_var_exp "y"))
                                             (V.integer_var_exp "z"))) then
            TestBed.add_neg_test ~testbed:tb [IntList l]
          else
            TestBed.add_pos_test ~testbed:tb [IntList l]
        )
      ~init:(
        TestBed.create_positive
          []
          ~args:sygus.synth_variables
          ~post:(fun _ res ->
              match res with
              | Ok v when v = Value.Bool false -> true
              | _ -> false))
      all_inside_examples
  in
  let myend = Option.value_exn (V.synth ~consts:sygus.constants testbed) in
    (V.to_string myend)*)
end
