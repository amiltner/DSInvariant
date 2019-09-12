open Core

open Utils

module T : Verifier.t = struct
  let _MAX_SIZE_T_ = 35
  let _MAX_SIZE_NON_T = 10

  type 'a condition =
    (*| Set of (int -> 'a list)*)
    | Predicate of ('a -> bool)

  let rec generator
      (tc:Context.Types.t)
      (t:Type.t)
      (pos:Value.t condition)
      (neg:Value.t condition)
      (size:int)
    : Expr.t list =
    let generator_simple t size = generator tc t pos neg size in
    if Type.equal t Type._t then
      failwith "ahh too hard"
    else
      begin match t with
        | Named i ->
          generator_simple
            (Context.find_exn tc i)
            size
        | Arrow (_,_) -> failwith "ah"
        | _ -> failwith "ah"
      end

  and verifier
      (tc:Context.Types.t)
      (t:Type.t)
      (pos:Value.t condition)
      (neg:Value.t condition)
      (vs:Value.t list)
    : (Expr.t list * Expr.t list) =
    let verifier_simple t vs = verifier tc t pos neg vs in
    if Type.equal t Type._t then
      failwith "ahh too hard"
    else
      begin match t with
        | Named i -> verifier_simple (Context.find_exn tc i) vs
        | Arrow (t1,t2) ->
          let t1_generateds = generator tc t1 neg pos _MAX_SIZE_T_ in
          let new_vs =
            List.map
              ~f:(fun (f,x) -> (Eval.evaluate (Expr.mk_app (Value.to_exp f) x)))
              (List.cartesian_product vs t1_generateds)
          in
          verifier_simple t2 new_vs
        | Tuple ts ->
          let eis =
            List.transpose_exn
              (List.map ~f:Value.destruct_tuple_exn vs)
          in
          let ts_eis =
            List.zip_exn
              ts
              eis
          in
          List.fold
            ~f:(fun (acc_ins,acc_outs) (t,vs) ->
                let (ins,outs) = verifier_simple t vs in
                (ins@acc_ins,outs@acc_outs))
            ~init:([],[])
            ts_eis
        | Mu (i,t) ->
          let tc = Context.set tc ~key:i ~data:t in
          verifier tc t pos neg vs
        | Variant branches ->
          let c_vs = List.map ~f:(Value.destruct_ctor_exn) vs in
          let c_vs_sorted =
            List.sort
              ~compare:(fun (c1,_) (c2,_) -> Id.compare c1 c2)
              c_vs
          in
          let c_vs_grouped =
            List.group
              ~break:(fun (c1,_) (c2,_) -> String.equal c1 c2)
              c_vs_sorted
          in
          List.fold
            ~f:(fun (acc_ins,acc_outs) cvs ->
                let c = fst (List.hd_exn cvs) in
                let vs = List.map ~f:snd cvs in
                let t = List.Assoc.find_exn ~equal:String.equal branches c in
                let (ins,outs) = verifier_simple t vs in
                (ins@acc_ins,outs@acc_outs))
            ~init:([],[])
            c_vs_grouped
      end

  let equiv_false
      ~(problem:Problem.t)
      ~cond:(cond:Expr.t)
    : bool =
    let cond_t = Type.mk_arrow (Type._t) (Type._bool) in
    try
      let (_,_) =
        verifier
          problem.tc
          cond_t
          (Predicate (fun _ -> false))
          (Predicate (fun v -> if Value.equal v Value.mk_true then raise Caml.Exit else true))
          [Eval.evaluate_with_holes ~eval_context:problem.eval_context cond]
      in
      true
    with Caml.Exit -> false

  module IntToExpr = struct
    include Map.Make(Int)
    include Provide_bin_io(Int)
    include Provide_hash(Int)
  end

  let true_on_examples
      ~problem:(_:Problem.t)
      ~(examples:Value.t list)
      ~eval:(_:Expr.t)
      ~eval_t:(_:Type.t)
      ~(post:UniversalFormula.t)
    : Value.t list =
    let (_,_) = UniversalFormula.to_expr_and_type post in
    let size_dict =
      List.fold
        ~f:(fun d v ->
            let i = Value.size v in
            IntToExpr.update
              ~f:(fun vo ->
                  begin match vo with
                    | None -> [v]
                    | Some vs -> v::vs
                  end)
              d
              i)
        ~init:IntToExpr.empty
        examples
    in
    let _ =
      fun i ->
        Option.value
          ~default:[]
          (IntToExpr.find
             size_dict
             i)
    in
    (*verifier
      problem.tc
      t
      (Set size_func)*)
    failwith "ah"

  let implication_counter_example
      ~problem:(_:Problem.t)
      ~pre:(_:Expr.t)
      ~eval:(_:Expr.t)
      ~eval_t:(_:Type.t)
      ~post:(_:UniversalFormula.t)
    : Value.t list =
    failwith "ah"
    (*let desired_t = Type._t in
    let (args_t,result_t) = extract_args eval_t in
    if not (contains_any problem.tc desired_t result_t) then
      []
    else
      List.fold
        ~f:(fun ans_o s ->
            begin match ans_o with
              | Some ans -> Some ans
              | None ->
                let examples =
                  if List.mem ~equal:Type.equal args_t desired_t then
                    List.filter_map
                      ~f:(fun e ->
                          let pre_e_app =
                            Expr.mk_app
                              pre
                              e
                          in
                          let v = Eval.evaluate_with_holes ~eval_context:problem.eval_context pre_e_app in
                          if Value.equal v Value.mk_true then
                            Some (Value.from_exp_exn e)
                          else if Value.equal v Value.mk_false then
                            None
                          else
                            failwith "incorrect evaluation")
                      (elements_of_type_to_size problem.tc desired_t s)
                  else
                    []
                in
                let results =
                  true_on_examples_full
                    ~problem
                    ~examples
                    ~eval
                    ~eval_t
                    ~post
                    ~size:s
                in
                Option.map
                  ~f:(List.concat_map
                        ~f:(fun (ets,_) ->
                            List.filter_map
                              ~f:(fun (e,t) ->
                                  if Type.equal t desired_t then
                                    Some (Value.from_exp_exn e)
                                  else
                                    None)
                              ets))
                  results
            end)
        ~init:None
        [_MAX_SIZE_T_ / 2; Float.to_int (Float.of_int (_MAX_SIZE_T_) /. 1.25) ; _MAX_SIZE_T_]*)
end
