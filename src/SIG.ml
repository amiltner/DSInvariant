open MyStdlib

open SyGuS
open Utils
open SetVPie
open Verifiers

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

let satisfyTrans
    (type t)
    ~verifier:(module V : Verifier with type t = t)
    ~(inv : t)
    ~(conf : Value.t list config)
    ~(sygus : SyGuS.t)
    ~(states : Value.t list list)
  : (V.t * model option) =
  let invf_call = V.true_exp
    (*"(invf "
    ^ (List.to_string_map sygus.inv_func.args ~sep:" " ~f:fst)
      ^ ")" *)in
  let _(*invf'_call*) =
    "(invf "
    ^ (List.to_string_map sygus.inv_func.args ~sep:" " ~f:(fun (s, _) -> s ^ "!"))
    ^ ")" in
  let eval = V.true_exp in
    (*if not (conf.model_completion_mode = `UsingZ3) then
      (*"true"*)
    else
       "(and " ^ (V.to_string invf_call) ^ " " ^ sygus.trans_func.expr ^ ")" in*)
  let rec helper (inv : t) : (V.t * model option) =
    Log.info
      (lazy ("IND >> Strengthening for inductiveness:"
             ^ (Log.indented_sep 4)
             ^ (V.to_string inv))) ;
    if V.equal inv V.false_exp then
      (V.false_exp, None)
    else
      let (* inv_def *) _ =
        "(define-fun invf ("
        ^ (List.to_string_map
             sygus.inv_func.args
             ~sep:" "
             ~f:(fun (s, t) -> "(" ^ s ^ " " ^ (Type.to_string t) ^ ")"))
        ^ ") Bool "
        ^ (V.to_string inv)
        ^ ")"
      in
      (*ZProc.create_scope
        z3
        ~db:[ inv_def
            ; "(assert " ^ sygus.trans_func.expr ^ ")"
            ; "(assert " ^ invf_call ^ ")" ];*)
      let pre_inv =
        SetVPie.learnVPreCond
          ~verifier:(module V)
          ~conf:conf.for_VPIE
          ~eval
          ~consts:sygus.constants
          ~post:invf_call
          (*~eval_term
            ~post_desc:invf'_call*)
          ~testbed:(TestBed.create_positive
                  states
             ~args:sygus.synth_variables
             ~post:(fun _ res ->
                 match res with
                 | Ok v when v = Value.Bool false -> true
                 | _ -> false))
      in
      Log.debug (lazy ("IND Delta: " ^ (V.to_string pre_inv))) ;
      if V.equal pre_inv V.true_exp then
        (inv, None)
      else
        begin
          let new_inv = V.and_exps pre_inv inv in
          Log.info
            (lazy ("PRE >> Checking if the following candidate is weaker than precond:"
                   ^ (Log.indented_sep 4) ^ (V.to_string new_inv))) ;
          let ce = None (*(ZProc.implication_counter_example z3 sygus.pre_func.expr new_inv)*) in
          if ce = None then
            helper new_inv
          else
            (new_inv, ce)
        end
  in
  helper inv

let learnSetInvariant_internal
    (type t)
    ~verifier:(module V : Verifier with type t = t)
    ~(conf : Value.t list config)
    ~(restarts_left : int)
    ~(states : Value.t list list)
    ~(sygus : SyGuS.t)
    ~(seed_string : string)
    ~(prop:V.t)
  : V.t =
  let rec strengthen_invariant
      ~(restarts_left : int)
      ~(states : Value.t list list)
      ~(code:V.t)
      ~(seed_string : string)
      ~(prop:V.t)
    : V.t =
    let open Quickcheck in
    let open SetSimulator in
    let restart_with_new_states head : V.t =
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
          strengthen_invariant
            ~restarts_left:(restarts_left - 1) 
            ~states:List.(dedup_and_sort ~compare:(compare Value.compare) (
                states @ (random_value ~size:conf.max_steps_on_restart ~seed:(`Deterministic seed_string)
                            (simulate_from sygus head))))
            ~code
            ~seed_string:(seed_string ^ "#")
            ~prop:prop
        end
    in
    let initial_inv =
      SetVPie.learnVPreCond
        ~verifier:(module V)
        ~conf:conf.for_VPIE
        ~eval:V.true_exp (*TODO: fix*)
        ~post:prop
        ~consts:sygus.constants
        ~testbed:(TestBed.create_positive states
           ~args:sygus.synth_variables
           ~post:(fun _ res ->
               match res with
               | Ok v when v = Value.Bool false -> true
               | _ -> false))
    in
    match satisfyTrans ~verifier:(module V) ~conf ~sygus ~states ~inv:initial_inv with
    | inv, None ->
      if not (V.equal inv V.false_exp) then
        (*ZProc.simplify z3 inv*) inv
      else
        restart_with_new_states
          (random_value
             ~seed:(`Deterministic seed_string)
             (failwith "hello"))
    (*(gen_pre_state ~use_trans:true sygus))*)
    | _, (Some ce_model) ->
      restart_with_new_states
        (random_value
           ~seed:(`Deterministic seed_string)
           (gen_state_from_model sygus (Some ce_model)))
  in
  let prop =
    strengthen_invariant
      ~restarts_left
      ~states
      ~code:V.true_exp (* TODO: fix *)
      ~seed_string
      ~prop
  in
  strengthen_invariant
    ~restarts_left
    ~states
    ~code:V.true_exp (* TODO: fix *)
    ~seed_string
    ~prop

let learnSetInvariant
    ?(conf = default_config)
    ~(states : Value.t list list)
    (sygus : SyGuS.t)
  : Job.desc =
  let find_from_verifier
      ~verifier:(module V : Verifier)
    : Job.desc =
    V.to_string
      (learnSetInvariant_internal
         ~verifier:(module V)
         ~conf
         ~restarts_left:conf.max_restarts
         ~states
         ~sygus
         ~seed_string:conf.base_random_seed
         ~prop:V.true_exp)
  in
  let verifier =
    begin match conf.verifier with
      | `QuickCheck -> failwith "unimplemented"
      | `Z3 -> z3_verifier
    end
  in
  find_from_verifier ~verifier
