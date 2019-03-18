open Core_kernel
open Verifiers

open Utils

module SetVPieImpl(V : Verifier) =
struct
  module SetSimulator = SetSimulator.SetSimulatorImpl(V)
  type 'a config = {
    for_SPIE : SPIE.config ;

    base_random_seed : string ;
    describe : (('a TestBed.feature TestBed.with_desc) CNF.t option) -> TestBed.desc ;
    max_tries : int ;
    simplify : bool ;
  }

  let default_config = {
    for_SPIE = SPIE.default_config ;
    base_random_seed = "VPIE" ;
    describe = SPIE.cnf_opt_to_desc ;
    max_tries = 512 ;
    simplify = true ;
  }

  let learnVPreCond
      ~(pre:V.expr)
      ~(conf : Value.t list config)
      ~(eval : V.expr)
      ~(post : V.expr)
      ~(consts:Value.t list)
      ~(testbed : TestBed.t)
    : V.expr =
    let oldpre = pre in
    let rec helper
        (tries_left:int)
        (testbed:TestBed.t)
      : V.expr option =
      if conf.max_tries > 0 && tries_left < 1 then
        (Log.error (lazy ("VPIE Reached MAX attempts ("
                          ^ (Int.to_string conf.max_tries)
                          ^ "). Giving up ..."));
         None)
      else
        (Log.info (lazy ("VPIE Attempt "
                         ^ (Int.to_string (1 + conf.max_tries - tries_left))
                         ^ "/" ^ (Int.to_string conf.max_tries) ^ "."));
         let pos_examples = List.map ~f:(fun (v,_) -> List.hd_exn v) testbed.pos_tests in
         let neg_examples = List.map ~f:(fun (v,_) -> List.hd_exn v) testbed.neg_tests in
         let basic_examples =
           List.map
             ~f:(fun x -> match x with
                 | IntList l -> l
                 | _ -> failwith "nope")
             (pos_examples@neg_examples)
         in
         let rec sublists = function
           | []    -> [[]]
           | x::xs -> let ls = sublists xs in
             (x::xs)::ls
         in
         let all_inside_examples =
           List.concat_map
             ~f:sublists
             basic_examples
         in
         let testbed =
           List.fold_left
             ~f:(fun tb l ->
                 if Option.is_some (SetSimulator.check_condition_held_after_eval
                                        ~test:[("x",Type.INTLIST, IntList l)]
                                        ~code:eval
                                        ~condition:post) then
                   TestBed.add_neg_test ~testbed:tb [IntList l]
                 else
                   TestBed.add_pos_test ~testbed:tb [IntList l]
              )
             ~init:(TestBed.create_positive ~args:(List.zip_exn testbed.farg_names testbed.farg_types) ~post:testbed.post [])
             all_inside_examples
         in
         match V.synth ~consts testbed with
         | None -> None
         | Some pre ->
           let testpre = V.bin_and_exps pre oldpre in
           Log.info (lazy ("Candidate Precondition: " ^ (V.to_string pre)));
           begin match V.implication_counter_example ~resultant:false ~pre:testpre ~eval ~post None with
             | None ->
               let pre = if conf.simplify then
                   V.simplify pre
                 else
                   pre
               in
               Log.info (lazy ("Verified Precondition: " ^ (V.to_string pre)));
               Some pre
             | Some model ->
               let model = Hashtbl.Poly.of_alist_exn model in
               let test =
                 List.map2_exn testbed.farg_names testbed.farg_types
                   ~f:(fun n t -> match Hashtbl.find model n with
                       | Some v -> v
                       | None ->
                         let open Quickcheck in
                         random_value (TestGen.for_type t)
                           ~size:1
                           ~seed:(`Deterministic (
                               conf.base_random_seed ^
                               (string_of_int tries_left))))
               in
               Log.info
                 (lazy ("Counter example: {"
                        ^ (List.to_string_map2
                             test testbed.farg_names
                             ~sep:", "
                             ~f:(fun v n -> n ^ " = " ^ (Value.to_string v)))
                        ^ "}"));
               helper (tries_left - 1) (TestBed.add_neg_test ~testbed test)
           end)
    in
    begin match helper conf.max_tries testbed with
      | None -> V.false_exp
      | Some e -> e
    end
end
