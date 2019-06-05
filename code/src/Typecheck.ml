open Core

open Lang

let type_equiv
    (tc:TypeContext.t)
    (t1:Type.t)
    (t2:Type.t)
  : bool =
  let rec type_equiv_internal
      (tc1:TypeContext.t)
      (tc2:TypeContext.t)
      (t1:Type.t)
      (t2:Type.t)
    : bool =
    let replace_with_definition
        (tc:TypeContext.t)
        (v:Id.t)
      : Type.t =
      Context.find_exn tc v
    in
    let type_equiv_simple = type_equiv_internal tc1 tc2 in
    begin match (t1,t2) with
      | (Var i1, Var i2) ->
        if Id.equal i1 i2 then
          true
        else
          let t1 = replace_with_definition tc1 i1 in
          let t2 = replace_with_definition tc2 i2 in
          type_equiv_simple t1 t2
      | (Var i1, _) ->
        let t1 = replace_with_definition tc1 i1 in
        type_equiv_simple t1 t2
      | (_, Var i2) ->
        let t2 = replace_with_definition tc2 i2 in
        type_equiv_simple t1 t2
      | (Mu _, Mu _) ->
        Type.equal t1 t2
      | (Mu (i1,t1'), _) ->
        let tc1 = Context.set tc1 ~key:i1 ~data:t1 in
        type_equiv_internal tc1 tc2 t1' t2
      | (_, Mu (i2,t2')) ->
        let tc2 = Context.set tc2 ~key:i2 ~data:t2 in
        type_equiv_internal tc1 tc2 t1 t2'
      | (Arr (t11,t12), Arr (t21,t22)) ->
        let t1_equiv = type_equiv_simple t11 t21 in
        let t2_equiv = type_equiv_simple t12 t22 in
        t1_equiv && t2_equiv
      | (Arr _, _) -> false
      | (_, Arr _) -> false
      | (Tuple t1s, Tuple t2s) ->
        Option.value_map
          ~default:false
          ~f:(fun t1t2s ->
              List.fold_left
                ~f:(fun acc_b (t1,t2) ->
                    acc_b && type_equiv_simple t1 t2)
                ~init:true
                t1t2s)
          (List.zip t1s t2s)
      | (Tuple _, _) -> false
      | (_, Tuple _) -> false
      | (Variant idts1, Variant idts2) ->
        Option.value_map
          ~default:false
          ~f:(fun t1t2s ->
              List.fold_left
                ~f:(fun acc_b ((id1,t1),(id2,t2)) ->
                    acc_b
                    && type_equiv_simple t1 t2
                    && Id.equal id1 id2)
                ~init:(true)
                t1t2s)
          (List.zip idts1 idts2)
    end
  in
  type_equiv_internal tc tc t1 t2

let rec concretify
    (tc:TypeContext.t)
    (t:Type.t)
  : Type.t =
  begin match t with
    | Var i ->
      concretify tc (Context.find_exn tc i)
    | Mu (i, t') ->
      let tc = Context.set tc ~key:i ~data:t in
      concretify tc t'
    | _ -> t
  end

let rec typecheck_exp
    (ec:ExprContext.t)
    (tc:TypeContext.t)
    (vc:VariantContext.t)
    (e:Expr.t)
  : Type.t =
  let typecheck_simple = typecheck_exp ec tc vc in
  begin match e with
    | Var v ->
      Context.find_exn ec v
    | App (e1,e2) ->
      let t1 = concretify tc (typecheck_simple e1) in
      let (t11,t12) = Type.destruct_arr_exn t1 in
      let t2 = typecheck_simple e2 in
      if type_equiv tc t11 t2 then
        t12
      else
        failwith ("applied invalid type: "
                  ^ (Type.show t2)
                  ^ " instead of "
                  ^ (Type.show t11))
    | Func ((i,t),e) ->
      let ec = Context.set ec ~key:i ~data:t in
      Type.mk_arr
        t
        (typecheck_exp
           ec
           tc
           vc
           e)
    | Ctor (i,e) ->
      let t = typecheck_simple e in
      let its = Context.find_exn vc i in
      let t_defined =
        List.Assoc.find_exn ~equal:Id.equal its i
      in
      if type_equiv tc t_defined t then
        Type.mk_variant its
      else
        failwith ("variant " ^ i ^ "expects different type")
    | Match(e,i,branches) ->
      let t = concretify tc (typecheck_simple e) in
      let expected_branches = Type.destruct_variant_exn t in
      let ordered_expected =
        List.sort
          ~compare:(fun (i1,_) (i2,_) -> Id.compare i1 i2)
          expected_branches
      in
      let ordered_actual =
        List.sort
          ~compare:(fun (i1,_) (i2,_) -> Id.compare i1 i2)
          branches
      in
      let merged_ordered_actual_expected =
        List.zip_exn ordered_actual ordered_expected
      in
      Option.value_exn
        (List.fold_left
           ~f:(fun acc_o ((i_actual,e),(i_expected,t_arg)) ->
               if Id.equal i_actual i_expected then
                 let ec = Context.set ec ~key:i ~data:t_arg in
                 let t = typecheck_exp ec tc vc e
                  in begin match acc_o with
                       | None -> Some t
                       | Some acc
                         -> if (type_equiv tc acc t) then
                              Some acc
                            else failwith
                                   ("inconsistent return types: "
                                   ^ (Type.show acc)
                                   ^ " and "
                                   ^ (Type.show t))
                     end
               else
                 failwith
                   ("Variant mismatch with "
                    ^ i_actual
                    ^ " and "
                    ^ i_expected))
           ~init:None
           merged_ordered_actual_expected)
    | Fix (i,t,e) ->
      let ec = Context.set ec ~key:i ~data:t in
      typecheck_exp ec tc vc e
    | Tuple es ->
      Type.mk_tuple
        (List.map
           ~f:typecheck_simple
           es)
    | Proj (i,e) ->
      let t = concretify tc (typecheck_simple e) in
      let ts = Type.destruct_tuple_exn t in
      List.nth_exn ts i
  end

let typecheck_formula
    (ec:ExprContext.t)
    (tc:TypeContext.t)
    (vc:VariantContext.t)
    ((foralls,e):UniversalFormula.t)
  : Type.t list =
  let (ec,ts) =
    List.fold_left
      ~f:(fun (ec,ts) (i,t) ->
          (Context.set ec ~key:i ~data:t, t::ts))
      ~init:(ec,[])
      foralls
  in
  let t =
    typecheck_exp
      ec
      tc
      vc
      e
  in
  let equiv = type_equiv tc t (Type.mk_var "bool") in
  if equiv then
    ts
  else
    failwith "universal formula was not a proposition"

let rec align_types
    (t:Type.t)
    (e:Expr.t)
  : Expr.t =
  begin match (t,e) with
    | (_, Expr.Fix (i,_,e)) ->
      Expr.mk_fix i t (align_types t e)
    | (Type.Arr (t1,t2), Expr.Func ((i,_),e)) ->
      Expr.mk_func (i,t1) (align_types t2 e)
    | _ -> e
  end
