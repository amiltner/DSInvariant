open MyStdlib
open Verifiers
open Lang

module Make(V : Verifier) =
struct
  let learnVPreCond
      ~(problem:problem)
      ~(pre:Expr.t)
      ~(eval : Expr.t)
      ~(post : UniversalFormula.t)
      ~(positives : Value.t list)
    : Expr.t =
    let testbed = TestBed.create_positive positives in
    let rec helper
        (attempt:int)
        (testbed:TestBed.t)
      : Expr.t =
        (Log.info (lazy ("VPIE Attempt "
                         ^ (Int.to_string attempt)
                         ^ "."));
         (*let pos_examples = List.map ~f:(fun (v,_) -> List.hd_exn v) testbed.pos_tests in
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
                        ~problem
                        ~examples:(*[V.from_value (IntList l)]*) (failwith "ah")
                        ~eval:eval
                        ~post:post) then
                   TestBed.add_neg_tests ~testbed:tb [IntList l]
                 else
                   TestBed.add_pos_test ~testbed:tb [IntList l]
              )
             ~init:(TestBed.create_positive ~args:(List.zip_exn testbed.farg_names testbed.farg_types) ~post:testbed.post [])
             all_inside_examples
           in*)
         let synthed_pre = Option.value_exn (V.synth ~problem ~testbed) in
         Log.info (lazy ("Candidate Precondition: " ^ (Expr.show synthed_pre)));
         let full_pre = Expr.and_predicates pre synthed_pre in
         begin match V.implication_counter_example ~problem ~pre:full_pre ~eval:eval ~post:post with
           | None ->
             Log.info (lazy ("Verified Precondition: " ^ (Expr.show synthed_pre)));
             pre
           | Some model ->
             if (List.length model <> 1) then
               failwith ("cannot do such functions yet: " ^ (string_of_list Value.show model))
             else
               helper
                 (attempt+1)
                 (TestBed.add_neg_test_disallow_dups
                    ~testbed
                    (List.hd_exn model))
           end)
    in
    helper 0 testbed
end
