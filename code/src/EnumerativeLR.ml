open Core
open Utils

module T : LR.t = struct
  let _MAX_SIZE_T_ = 35
  let _MAX_SIZE_NON_T = 10

  type 'a internal_condition =
    | InternalSet of ((int -> 'a list) * 'a list)
    | InternalPredicate of ('a -> bool)

  let check_condition
      (c:'a internal_condition)
      (x:'a)
    : bool =
    begin match c with
      | InternalSet (_,xs) -> List.mem ~equal:(=) xs x
      | InternalPredicate p -> p x
    end

  open LR

  let rec extract_typed_subcomponents
      (tc:Context.Types.t)
      (desired_t:Type.t)
      (t:Type.t)
      (v:Value.t)
    : Value.t list =
    let extract_typed_subcomponents_simple = extract_typed_subcomponents tc desired_t in
    if Type.equal t desired_t then
      [v]
    else
      begin match (t,v) with
        | (Tuple ts, Tuple vs) ->
          List.concat_map
            ~f:(fun (t,v) -> extract_typed_subcomponents_simple t v)
            (List.zip_exn ts vs)
        | (Variant branches, Ctor (c,v)) ->
          let t =
            List.Assoc.find_exn ~equal:String.equal branches c
          in
          extract_typed_subcomponents_simple t v
        | (Named i, _) ->
          begin match Context.find tc i with
            | None -> []
            | Some t -> extract_typed_subcomponents_simple t v
          end
        | (Mu (i,t), _) ->
          let tc = Context.set tc ~key:i ~data:t in
          extract_typed_subcomponents tc desired_t t v
        | (Arrow _, _) -> failwith "arrows not currently supported"
        | _ -> failwith "Something went wrong"
      end

  let rec generator
      (tc:Context.Types.t)
      (t:Type.t)
      (pos:Value.t internal_condition)
      (neg:Value.t internal_condition)
      (size:int)
    : Value.t list =
    let generator_simple t size = generator tc t pos neg size in
    if Type.equal t Type._t then
      begin match pos with
        | InternalSet (is,_) -> is size
        | InternalPredicate p ->
          let unpredicated =
            generator_simple
              (Context.find_exn tc "t")
              size
          in
          List.filter ~f:p unpredicated
      end
    else
      begin match t with
        | Named i ->
          generator_simple
            (Context.find_exn tc i)
            size
        | Arrow (_,_) -> failwith "ah"
        | Tuple ts ->
          let parts = List.partitions (size-1) (List.length ts) in
          let components =
            List.concat_map
              ~f:(fun part ->
                  let components =
                    List.map2_exn
                      ~f:(fun t p -> generator_simple t p)
                      ts
                      part
                  in
                  List.combinations components)
              parts
          in
          List.map ~f:Value.mk_tuple components
        | Mu (v,t) ->
          let tc = Context.set tc ~key:v ~data:t in
          generator tc t pos neg size
        | Variant options ->
          List.concat_map
            ~f:(fun (i,t) ->
                List.map
                  ~f:(Value.mk_ctor i)
                  (generator_simple t (size-1)))
            options
      end

  and verifier
      (tc:Context.Types.t)
      (t:Type.t)
      (pos:Value.t internal_condition)
      (neg:Value.t internal_condition)
      (vs:(Value.t list * Value.t) list)
    : (Value.t list * Value.t list) =
    let verifier_simple t vs = verifier tc t pos neg vs in
    if Type.equal t Type._t then
      let bads =
        List.filter
          ~f:(fun (_,f) -> not (check_condition pos f))
          vs
      in
      let (bads_pres,bads_post) =
        List.unzip
          bads
      in
      (List.concat bads_pres, bads_post)
    else
      begin match t with
        | Named i -> verifier_simple (Context.find_exn tc i) vs
        | Arrow (t1,t2) ->
          let t1_generateds = generator tc t1 neg pos _MAX_SIZE_T_ in
          let new_vs =
            List.map
              ~f:(fun ((_,f),x) ->
                  let subcomponents =
                    extract_typed_subcomponents
                      tc
                      Type._t
                      t1
                      x
                  in
                  (subcomponents, (Eval.evaluate (Expr.mk_app (Value.to_exp f) (Value.to_exp x)))))
              (List.cartesian_product vs t1_generateds)
          in
          verifier_simple t2 new_vs
        | Tuple ts ->
          let eis =
            List.transpose_exn
              (List.map
                 ~f:(fun (pres,cur) ->
                     let curs =
                       Value.destruct_tuple_exn
                         cur
                     in
                     List.map
                       ~f:(fun cur -> (pres,cur))
                       curs)
                 vs)
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
          let c_vs =
            List.map
              ~f:(fun (pres,v) ->
                  let (i,vs) = Value.destruct_ctor_exn v in
                  (i,pres,vs)
                ) vs in
          let c_vs_sorted =
            List.sort
              ~compare:(fun (c1,_,_) (c2,_,_) -> Id.compare c1 c2)
              c_vs
          in
          let c_vs_grouped =
            List.group
              ~break:(fun (c1,_,_) (c2,_,_) -> String.equal c1 c2)
              c_vs_sorted
          in
          List.fold
            ~f:(fun (acc_ins,acc_outs) cvs ->
                let c = fst3 (List.hd_exn cvs) in
                let vs = List.map ~f:(fun (_,pres,v) -> (pres,v)) cvs in
                let t = List.Assoc.find_exn ~equal:String.equal branches c in
                let (ins,outs) = verifier_simple t vs in
                (ins@acc_ins,outs@acc_outs))
            ~init:([],[])
            c_vs_grouped
      end

  module IntToExpr = struct
    include Map.Make(Int)
    include Provide_bin_io(Int)
    include Provide_hash(Int)
  end

  let verifier
        ~(problem:Problem.t)
        (t:Type.t)
        (pos:Value.t condition)
        (neg:Value.t condition)
        (v:Value.t)
    : (Value.t list * Value.t list) =
    let to_internal_condition
        (c:Value.t condition)
      : Value.t internal_condition =
      begin match c with
        | Set vs ->
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
              vs
          in
          let size_func =
            fun i ->
              Option.value
                ~default:[]
                (IntToExpr.find
                   size_dict
                   i)
          in
          InternalSet (size_func,vs)
        | Predicate f -> InternalPredicate f
      end
    in
    verifier
      problem.tc
      t
      (to_internal_condition pos)
      (to_internal_condition neg)
      [[],v]
end
