open Core_kernel
open Verifiers

open Utils

module Make(V : Verifier) =
struct
  module SetSimulator = SetSimulator.SetSimulatorImpl(V)

  let learnVPreCond
      ~(pre:V.expr)
      ~(eval : V.expr)
      ~(post : V.expr)
      ~(consts:Value.t list)
      ~(testbed : TestBed.t)
    : V.expr =
    let oldpre = pre in
    let rec helper
        (attempt:int)
        (testbed:TestBed.t)
      : V.expr =
        (Log.info (lazy ("VPIE Attempt "
                         ^ (Int.to_string attempt)
                         ^ "."));
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
         let pre = Option.value_exn (V.synth ~consts testbed) in
         let testpre = V.bin_and_exps pre oldpre in
         Log.info (lazy ("Candidate Precondition: " ^ (V.to_string pre)));
         begin match V.implication_counter_example ~resultant:false ~pre:testpre ~eval ~post None with
           | None ->
             let pre = V.simplify pre in
             Log.info (lazy ("Verified Precondition: " ^ (V.to_string pre)));
             pre
           | Some model ->
             let model = Hashtbl.Poly.of_alist_exn model in
             let test =
               List.map2_exn testbed.farg_names testbed.farg_types
                 ~f:(fun n _ -> Hashtbl.find_exn model n)
             in
             Log.info
               (lazy ("Counter example: {"
                      ^ (List.to_string_map2
                           test testbed.farg_names
                           ~sep:", "
                           ~f:(fun v n -> n ^ " = " ^ (Value.to_string v)))
                      ^ "}"));
             helper (attempt+1) (TestBed.add_neg_test ~testbed test)
         end)
    in
    helper 0 testbed
end
