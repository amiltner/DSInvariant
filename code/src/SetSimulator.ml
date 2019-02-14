open Core_kernel
open Verifiers
open SyGuS_Set
open Utils

let setup (_ : SyGuS_Set.t) : unit =
  ()(*ignore (ZProc.run_queries ~scoped:false z3 ~db:((
    ("(set-logic " ^ s.logic ^ ")")
    :: (List.map ~f:fst(*var_declaration*) s.variables))
      @ (List.map ~f:(fun _ -> "")(*func_definition*) s.functions)) [])*)

let filter_state ?(trans = true) (model : ZProc.model) : ZProc.model =
  if trans
  then List.filter_map model
                       ~f:(fun (n, v) -> match String.chop_suffix n ~suffix:"!" with
                                         | None -> None
                                         | Some n -> Some (n, v))
  else List.filter model ~f:(fun (n, _) -> not (String.is_suffix n ~suffix:"!"))

let value_assignment_constraint ?(negate = false) ?(prime = false) (vars : var list)
                                (vals : Value.t list) : string =
  (if negate then "(not (and " else "(and ")
 ^ (List.to_string_map2 vars vals ~sep:" "
                        ~f:(fun (name, _) value ->
                              ("(= " ^ name ^ (if prime then "!" else "")
                               ^ " " ^ (Value.to_string value) ^ ")")))
 ^ (if negate then "))" else ")")

let gen_state_from_model (s : SyGuS_Set.t) (m : ZProc.model option)
                         : Value.t list option Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  match m with None -> singleton None
  | Some m -> create (fun ~size rnd -> Some (
                List.map s.synth_variables
                         ~f:(fun (v, t) ->
                               match List.Assoc.find m v ~equal:(=)
                               with Some d -> d
                                  | None -> generate (TestGen.for_type t) ~size rnd)))

let transition (s : SyGuS_Set.t) ((* vals *)_ : Value.t list)
               : Value.t list option Quickcheck.Generator.t =
  gen_state_from_model s (
    try begin
      match None (* ZProc.sat_model_for_asserts z3
              ~db:[ ("(assert " ^ s.trans_func.expr ^ ")")
                  ; ( "(assert (and "
                    ^ (Utils.List.to_string_map2 ~sep:" " vals s.synth_variables
                        ~f:(fun d (v, _) -> ("(= " ^ v ^ " " ^
                                            (Value.to_string d) ^ ")")))
                    ^ "))")] *)
      with None -> None | Some model -> Some (filter_state ~trans:true model)
    end with _ -> None)

let gen_pre_state
    ~verifier:(module V : Verifier)
    ?(avoid = [])
    ?(use_trans = false)
    (s : SyGuS_Set.t)
  : Value.t list option Quickcheck.Generator.t =
  (*TODO*)
  assert (avoid = []);
  assert (use_trans = false);
  Log.info (lazy "Generating an initial state:");
  gen_state_from_model s
    (V.sat_model_for_asserts
          ~db:[ (*"(assert (and " ^ s.pre_func.expr ^ " "
              ^ (if use_trans then s.trans_func.expr else "true") ^ " "
                  ^ (String.concat avoid ~sep:" ") ^ "))"*) ]
          ~eval_term:V.true_exp)

let simulate_from (s : SyGuS_Set.t) (head : Value.t list option)
                  : Value.t list list Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  match head with None -> singleton []
  | Some head ->
      let step head ~size rnd =
        let rec step_internal head size =
          Log.info (lazy (" > " ^ (List.to_string_map ~sep:", " ~f:Value.to_string head))) ;
          head :: (match size with
                  | 0 -> []
                  | n -> begin match generate (transition s head) ~size rnd
                               with Some next when next <> head
                                    -> step_internal next (n-1)
                                  | _ -> []
                        end)
        in step_internal head size
      in Log.info (lazy ("New execution (" ^ (List.to_string_map s.synth_variables ~sep:", " ~f:fst) ^ "):"))
       ; create (step head)

let build_avoid_constraints sygus head =
  Option.map head ~f:(value_assignment_constraint sygus.synth_variables ~negate:true ~prime:true)

let record_states
    ~verifier:(module V : Verifier)
    ?(avoid = [])
    ~size
    ~seed
    ~state_chan
    ~(zpath : string)
    (s : SyGuS_Set.t)
  : unit =
  let record_and_update avoid head size : (string list * int) =
    match head with
    | None -> (avoid, 0)
    | _ -> let states = Quickcheck.random_value ~size ~seed
                                                (simulate_from s head) in
           let [@warning "-8"] Some head = build_avoid_constraints s head in
           let open Core.Out_channel
           in List.iter states
                        ~f:(fun s -> output_string state_chan
                                       (List.to_string_map ~sep:"\t" ~f:Value.to_string s)
                                   ; newline state_chan)
            ; flush state_chan
            ; ((head :: avoid), (List.length states))
  in ZProc.process ~zpath
       ~random_seed:(Some (string_of_int (Quickcheck.(
                       random_value ~seed (Generator.small_non_negative_int)))))
       (fun _ -> setup s ;
          let rec helper avoid size =
            let open Quickcheck in
            let sz = size / 2 in
            let head_1 = random_value (gen_pre_state ~verifier:(module V) ~avoid s) ~seed in
            let (avoid, added_1) = record_and_update avoid head_1 sz in
            let head_2 = random_value (gen_pre_state ~verifier:(module V) ~avoid ~use_trans:true s)
                                      ~seed in
            let (avoid, added_2) = record_and_update avoid head_2 sz
            in (if added_1 = 0 && added_2 = 0 then ()
                else let remaining_size = size - (added_1 + added_2)
                      in if remaining_size > 0 then helper avoid remaining_size
                                               else ())
          in helper avoid size)
