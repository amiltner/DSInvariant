open Core
open Utils

module T : LR.t = struct
  let _MAX_SIZE_T_ = 35
  let _MAX_SIZE_MULTIPLE_T = 25

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

  let any_postcondition
      (tc:Context.Types.t)
      (t:Type.t)
    : bool =
    let rec any_postcondition_internal
        (tc:Context.Types.t)
        (ids:Id.t list)
        (t:Type.t)
      : bool =
      Type.equal t Type._t ||
      begin match t with
        | Named i ->
          if List.mem ~equal:Id.equal ids i then
            false
          else
            any_postcondition_internal
              tc
              (i::ids)
              (Context.find_exn
                 tc
                 i)
        | Arrow (_,t2) ->
          any_postcondition_internal
            tc
            ids
            t2
        | Tuple ts ->
          List.exists
            ~f:(any_postcondition_internal tc ids)
            ts
        | Mu _ -> false
        | Variant branches ->
          List.exists
            ~f:(fun (_,t) -> any_postcondition_internal tc ids t)
            branches
      end
    in
    any_postcondition_internal
      tc
      []
      t

  let precondition_count
      (tc:Context.Types.t)
      (t:Type.t)
    : int =
    let rec precondition_count_internal
        (tc:Context.Types.t)
        (ids:Id.t list)
        (t:Type.t)
      : int =
      begin match t with
        | Named i ->
          if List.mem ~equal:Id.equal ids i then
            0
          else
            precondition_count_internal
              tc
              (i::ids)
              (Context.find_exn
                 tc
                 i)
        | Arrow (t1,t2) ->
          let left = if any_postcondition tc t1 then 1 else 0 in
          let right = precondition_count_internal tc ids t2 in
          left+right
        | Tuple ts ->
          List.fold
            ~f:(fun acc t ->
                acc + (precondition_count_internal tc ids t))
            ~init:0
            ts
        | Mu _ -> 0
        | Variant branches ->
          List.fold
            ~f:(fun acc (_,t) ->
                max acc (precondition_count_internal tc ids t))
            ~init:0
            branches
      end
    in
    precondition_count_internal
      tc
      []
      t

  open LR

  (*let rec extract_typed_subcomponents
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
      end*)

  let rec generator
      (tc:Context.Types.t)
      (t:Type.t)
      (pos:Value.t internal_condition)
      (neg:Value.t internal_condition)
      (size:int)
    : Value.t list =
    if size <= 0 then
      []
    else
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
      (max_size:int)
      (pres:Value.t list)
      (v:Value.t)
    : (Value.t list * Value.t) option =
    let verifier_simple t v = verifier tc t pos neg max_size v in
    if Type.equal t Type._t then
      if not (check_condition pos v) then
        Some (pres,v)
      else
        None
    else if not (any_postcondition tc t) then
      None
    else
      begin match t with
        | Named i -> verifier_simple (Context.find_exn tc i) pres v
        | Arrow (t1,t2) ->
          let t1_generateds =
            Sequence.concat_map
              ~f:(fun s -> Sequence.of_list (generator tc t1 neg pos s))
              (Sequence.of_list (List.range 0 max_size))
          in
          let t1_generateds_tagged =
            Sequence.map
              ~f:(fun v -> Expr.mk_tagged t1 (Value.to_exp v))
              t1_generateds
          in
          List.fold_until_completion
            ~f:(fun t1s ->
                begin match Sequence.next t1s with
                  | None -> Second None
                  | Some (t1,t1s) ->
                    let (v,newpres) = Eval.evaluate ~tc (Expr.mk_app (Value.to_exp v) t1) in
                    begin match verifier_simple t2 (pres@newpres) v with
                      | None -> First t1s
                      | Some _ as vo -> Second vo
                    end
                end)
            t1_generateds_tagged
          (*let new_vs =
            List.map
              ~f:(fun ((subs,f),x) ->
                  let (v,newsubs) = (Eval.evaluate ~tc (Expr.mk_app (Value.to_exp f) x)) in
                  (subs@newsubs,v))
              (List.cartesian_product vs t1_generateds_tagged)
          in
            verifier_simple t2 new_vs*)
        | Tuple ts ->
          let vs = Value.destruct_tuple_exn v in
          let tsvs =
            List.zip_exn
              ts
              vs
          in
          List.fold_until_completion
            ~f:(fun tsvs ->
                begin match tsvs with
                  | [] -> Second None
                  | (t,v)::tsvs ->
                    begin match verifier_simple t pres v with
                      | None -> First tsvs
                      | Some _ as vo -> Second vo
                    end
                end)
            tsvs
        | Mu (i,t) ->
          let tc = Context.set tc ~key:i ~data:t in
          verifier tc t pos neg max_size pres v
        | Variant branches ->
          let (i,v) = Value.destruct_ctor_exn v in
          let t = List.Assoc.find_exn ~equal:Id.equal branches i in
          verifier_simple t pres v
          (*let c_vs =
            List.map
              ~f:(fun (pres,v) ->
                  let (i,v) = Value.destruct_ctor_exn v in
                  (i,pres,v))
              vs in
          let c_vs_sorted =
            List.sort
              ~compare:(fun (c1,_,_) (c2,_,_) -> Id.compare c1 c2)
              c_vs
          in
          let c_vs_grouped =
            List.group
              ~break:(fun (c1,_,_) (c2,_,_) -> not (String.equal c1 c2))
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
            c_vs_grouped*)
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
    let max_size =
      if precondition_count problem.tc t > 1 then
        _MAX_SIZE_MULTIPLE_T
      else
        _MAX_SIZE_T_
    in
    let ans =
      verifier
        problem.tc
        t
        (to_internal_condition pos)
        (to_internal_condition neg)
        max_size
        []
        v
    in
    begin match ans with
      | None -> ([],[])
      | Some (pres,v) -> (pres,[v])
    end
end
