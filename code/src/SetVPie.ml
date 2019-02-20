open Core_kernel
open Verifiers

open SPIE
open Utils

module SetVPieImpl(V : Verifier) =
struct
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
      ~(conf : Value.t list config)
      ~(eval : V.expr)
      ~(post : V.expr)
      ~(consts:Value.t list)
      ~(testbed : TestBed.t)
    : V.expr =
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
         match learnPreCond ~conf:conf.for_SPIE ~consts testbed with
         | None
         | Some [[]] -> None
         | precond ->
           let pre = V.from_synth precond in
           Log.info (lazy ("Candidate Precondition: " ^ (V.to_string pre)));
           begin match V.implication_counter_example ~pre ~eval ~post with
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
