open MyStdlib

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

(*
   x = Int.max_value
   y = Int.max_value
*)
let empty_call
    (type t)
    ~verifier:(module V : Verifier with type t = t)
  : V.t =
  failwith "ah"

(*
   z == x || z == y
*)
let lookup_code
    (type t)
    ~verifier:(module V : Verifier with type t = t)
  : V.t =
  failwith "ah"

(*
   x =
     if z < x then
       x
     else
       if z = x then
         y
       else
         if z = y then
           x
         else
           x
   y =
     if z < x then
       y
     else
       if z = x then
         Int.max_value
       else
         if z = y then
           Int.max_value
         else
           y
*)
let delete_function
    (type expr)
    ~verifier:(module V : Verifier with type expr = expr)
  : V.expr =
  failwith "ah"

(*
   x = if z <= x then z else x
   y = if z <= x then y else z
*)
let insert_code
    (type expr)
    ~verifier:(module V : Verifier with type expr = expr)
  : V.expr =
  failwith "ah"

let satisfyTrans
    (type expr)
    ~verifier:(module V : Verifier with type expr = expr)
    ~(invariant : expr)
    ~(code : expr)
    ~(conf : Value.t list config)
    ~(sygus : SyGuS_Set.t)
    ~(states : Value.t list list)
  : (V.expr * model option) =
  let invf_call = V.true_exp
    (*"(invf "
    ^ (List.to_string_map sygus.inv_func.args ~sep:" " ~f:fst)
      ^ ")" *)in
  let _(*invf'_call*) =
    "(invf "
    ^ (List.to_string_map (*sygus.inv_func.args*) [] ~sep:" " ~f:(fun (s, _) -> s ^ "!"))
    ^ ")" in
  let eval = code in
    (*if not (conf.model_completion_mode = `UsingZ3) then
      (*"true"*)
    else
       "(and " ^ (V.to_string invf_call) ^ " " ^ sygus.trans_func.expr ^ ")" in*)
  let rec helper (inv : expr) : (V.expr * model option) =
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
             [] (*sygus.inv_func.args*)
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
          ~v:(V.empty)
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
          let new_inv = V.bin_and_exps pre_inv inv in
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
  helper invariant

let learnSetInvariant_internal
    (type expr)
    (type t)
    ~verifier:(module V : Verifier with type expr = expr and type t = t)
    ~(conf : Value.t list config)
    ~(restarts_left : int)
    ~(states : Value.t list list)
    ~(sygus : SyGuS_Set.t)
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
    let v = V.empty in
    let (v,_) = V.register_func v sygus.insert_func in
    let (v,_) = V.register_func v sygus.delete_func in
    let (v,_) = V.register_func v sygus.lookup_func in
    let (v,post_decl) = V.register_func v sygus.post_func in
    let post_expr = V.make_app post_decl [V.integer_var_exp "x";V.integer_var_exp "y"] in
    let invariant =
      SetVPie.learnVPreCond
        ~verifier:(module V)
        ~conf:conf.for_VPIE
        ~eval:V.true_exp (*TODO: confirm this works *)
        ~post:post_expr (*sygus.post_func*)
        ~consts:sygus.constants
        ~v
        ~testbed:(TestBed.create_positive states
                    ~args:sygus.synth_variables
                    ~post:(fun _ res ->
                        match res with
                        | Ok v when v = Value.Bool false -> true
                        | _ -> false))
    in
    (* {I'} s = insert y s {I} *)
    let invariant =
      match satisfyTrans
              ~verifier:(module V)
              ~conf
              ~sygus
              ~states
              ~code:(insert_code ~verifier:(module V))
              ~invariant with
      | inv, None ->
        if not (V.equal inv V.false_exp) then
          V.simplify inv
        else
          failwith "I want to fail this";
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
    (* {I'} s = delete y s {I} *)
    let invariant =
      match satisfyTrans
              ~verifier:(module V)
              ~conf
              ~sygus
              ~states
              ~code:(delete_function ~verifier:(module V))
              ~invariant with
      | inv, None ->
        if not (V.equal inv V.false_exp) then
          V.simplify inv
        else
          failwith "I want to fail this";
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
    begin match V.implication_counter_example
                  ~v
                  ~pre:(V.true_exp)
                  ~eval:(V.true_exp) (*TODO: confirm this works *)
                  ~post:invariant with
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
    ?(conf = default_config)
    ~(states : Value.t list list)
    (sygus : SyGuS_Set.t)
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
         ~seed_string:conf.base_random_seed)
  in
  let verifier =
    begin match conf.verifier with
      | `QuickCheck -> failwith "unimplemented"
      | `Z3 -> z3_verifier
    end
  in
  find_from_verifier ~verifier
