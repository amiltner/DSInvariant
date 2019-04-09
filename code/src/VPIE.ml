open Core_kernel
open Verifiers
open Lang
open Utils

module Make(V : Verifier) =
struct
  let learnVPreCond
      ~(pre:Expr.t)
      ~(eval : Expr.t)
      ~(post : Expr.t)
      ~consts:(_:Value.t list)
      ~(testbed : TestBed.t)
    : Expr.t =
    let _(*oldpre*) = pre in
    let helper
        (attempt:int)
        (testbed:TestBed.t)
      : Expr.t =
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
         let _(*testbed*) =
           List.fold_left
             ~f:(fun tb l ->
                 if Option.is_some
                     (V.true_on_examples
                        ~examples:(*[V.from_value (IntList l)]*) (failwith "ah")
                        ~eval:eval
                        ~post:post) then
                   TestBed.add_neg_tests ~testbed:tb [IntList l]
                 else
                   TestBed.add_pos_test ~testbed:tb [IntList l]
              )
             ~init:(TestBed.create_positive ~args:(List.zip_exn testbed.farg_names testbed.farg_types) ~post:testbed.post [])
             all_inside_examples
         in
         let _ =
           Option.value_exn
             (V.synth
                ~examples:(failwith "ah")
                ~eval:(failwith "ah")
                ~post:(failwith "ah"))
         in
         (*let testpre = V.bin_and_exps pre oldpre in
           Log.info (lazy ("Candidate Precondition: " ^ (V.to_string pre)));*)
         (*begin match V.implication_counter_example ~resultant:false ~pre:testpre ~eval ~post None with
           | None ->
             let pre = V.simplify pre in
             Log.info (lazy ("Verified Precondition: " ^ (V.to_string pre)));
             pre
           | Some model ->
             helper (attempt+1) (TestBed.add_neg_tests ~testbed model)
           end)*)
         failwith "ah")
    in
    helper 0 testbed
end
