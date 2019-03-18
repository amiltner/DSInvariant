open MyStdlib
open Lang

let type_equiv
    (tc:TypeContext.t)
    (t1:Type.t)
    (t2:Type.t)
  : bool except =
  let rec type_equiv_internal
      (tc1:TypeContext.t)
      (tc2:TypeContext.t)
      (t1:Type.t)
      (t2:Type.t)
    : bool except =
    let replace_with_definition
        (tc:TypeContext.t)
        (v:Id.t)
      : Type.t except =
      option_to_except
        ~f:(fun () -> "Type variable " ^ v ^ " not found")
        (TypeContext.lookup tc v)
    in
    let type_equiv_simple = type_equiv_internal tc1 tc2 in
    begin match (t1,t2) with
      | (Var i1, Var i2) ->
        if is_equal @$ Id.compare i1 i2 then
          Left true
        else
          let t1_e = replace_with_definition tc1 i1 in
          let t1_t2_e =
            except_bind
              ~f:(fun t1 ->
                  except_map
                    ~f:(fun t2 -> (t1,t2))
                    (replace_with_definition tc2 i2))
              t1_e
          in
          except_bind
            ~f:(fun (t1,t2) -> type_equiv_simple t1 t2)
            t1_t2_e
      | (Var i1, _) ->
        let t1_e = replace_with_definition tc1 i1 in
        except_bind
          ~f:(fun t1 -> type_equiv_simple t1 t2)
          t1_e
      | (_, Var i2) ->
        let t2_e = replace_with_definition tc2 i2 in
        except_bind
          ~f:(fun t2 -> type_equiv_simple t1 t2)
          t2_e
      | (Mu _, Mu _) ->
        Left (is_equal @$ Type.compare t1 t2)
      | (Mu (i1,t1'), _) ->
        let tc1 = TypeContext.insert tc1 i1 t1 in
        type_equiv_internal tc1 tc2 t1' t2
      | (_, Mu (i2,t2')) ->
        let tc2 = TypeContext.insert tc2 i2 t2 in
        type_equiv_internal tc1 tc2 t1 t2'
      | (Arr (t11,t12), Arr (t21,t22)) ->
        except_bind
          ~f:(fun t1_equiv ->
              except_map
                ~f:(fun t2_equiv -> t1_equiv && t2_equiv)
                (type_equiv_simple t12 t22))
          (type_equiv_simple t11 t21)
      | (Arr _, _) -> Left false
      | (_, Arr _) -> Left false
      | (Tuple t1s, Tuple t2s) ->
        Option.value_map
          ~default:(Left false)
          ~f:(fun t1t2s ->
              List.fold_left
                ~f:(fun acc_b_e (t1,t2) ->
                    except_bind
                      ~f:(fun acc_b ->
                          except_map
                            ~f:(fun b -> acc_b && b)
                            (type_equiv_simple t1 t2))
                      acc_b_e)
                ~init:(Left true)
                t1t2s
            )
          (List.zip t1s t2s)
      | (Tuple _, _) -> Left false
      | (_, Tuple _) -> Left false
      | (Variant idts1, Variant idts2) ->
        Option.value_map
          ~default:(Left false)
          ~f:(fun t1t2s ->
              List.fold_left
                ~f:(fun acc_b_e ((id1,t1),(id2,t2)) ->
                    except_bind
                      ~f:(fun acc_b ->
                          except_map
                            ~f:(fun b ->
                                acc_b
                                && b
                                && (is_equal (Id.compare id1 id2)))
                            (type_equiv_simple t1 t2))
                      acc_b_e)
                ~init:(Left true)
                t1t2s
            )
          (List.zip idts1 idts2)
    end
  in
  type_equiv_internal tc tc t1 t2

let rec concretify
    (tc:TypeContext.t)
    (t:Type.t)
  : Type.t except =
  begin match t with
    | Var i ->
      let t_e =
        option_to_except
          ~f:(fun () -> "undefined type variable " ^ i)
          (TypeContext.lookup tc i)
      in
      except_bind
        ~f:(concretify tc)
        t_e
    | Mu (i, t') ->
      let tc = TypeContext.insert tc i t in
      concretify tc t'
    | _ -> Left t
  end

let rec typecheck_exp
    (ec:ExprContext.t)
    (tc:TypeContext.t)
    (vc:VariantContext.t)
    (e:Expr.t)
  : Type.t except =
  let typecheck_simple = typecheck_exp ec tc vc in
  begin match e with
    | Var v ->
      option_to_except
        ~f:(fun () -> "Use of undefined " ^ v)
        (ExprContext.lookup ec v)
    | App (e1,e2) ->
      let t1_e = typecheck_simple e1 in
      let t1_e = except_bind ~f:(concretify tc) t1_e in
      let t1arr_components_e =
        except_bind
          ~f:(fun t1 ->
              option_to_except
                ~f:(fun () -> "Tried to apply nonfunctional " ^ (Expr.show e1))
                (Type.destruct_arr t1))
          t1_e
      in
      let t1arr_components_t2_e =
        except_bind
          ~f:(fun (t11,t12) ->
              except_map
                ~f:(fun t2 -> (t11,t12,t2))
                (typecheck_simple e2))
          t1arr_components_e
      in
      except_bind
        ~f:(fun (t11,t12,t2) ->
            except_bind
              ~f:(fun b ->
                  if b then
                    Left t12
                  else
                    Right ("applied invalid type: " ^
                           (Type.show t2) ^ " instead of " ^ (Type.show t11)))
              (type_equiv tc t11 t2))
        t1arr_components_t2_e
    | Func ((i,t),e) ->
      let ec = ExprContext.insert ec i t in
      except_map
        ~f:(Type.mk_arr t)
        (typecheck_exp
           ec
           tc
           vc
           e)
    | Ctor (i,e) ->
      let t = typecheck_simple e in
      except_bind
        ~f:(fun t ->
            let containing_type_e =
              option_to_except
                ~f:(fun () -> "constructor " ^ i ^ " is undefined")
                (VariantContext.lookup vc i)
            in
            except_bind
              ~f:(fun its ->
                  let t_defined =
                    List.Assoc.find_exn
                      ~equal:(is_equal %% Id.compare)
                      its
                      i
                  in
                  except_bind
                    ~f:(fun b ->
                        if b then
                          Left (Type.variant its)
                        else
                          Right ("variant " ^ i ^ "expects different type"))
                    (type_equiv tc t_defined t))
              containing_type_e)
        t
    | Match(e,i,branches) ->
      let t_e = typecheck_simple e in
      let t_e = except_bind ~f:(concretify tc) t_e in
      let branches_expected_e =
        except_bind
          ~f:(fun t ->
              option_to_except
                ~f:(fun () -> "branch on non-variant value")
                (Type.destruct_variant t))
          t_e
      in
      let merged_ordered_actual_expected_e =
        except_bind
          ~f:(fun expected_branches ->
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
              option_to_except
                ~f:(fun () -> "number of variants and branches not equal")
                (List.zip ordered_actual ordered_expected))
          branches_expected_e
      in
      except_bind
        ~f:(fun merged_ordered_actual_expected ->
            except_map
              ~f:(fun t_o -> Option.value_exn t_o)
              (List.fold_left
                 ~f:(fun acc_o_e ((i_actual,e),(i_expected,t_arg)) ->
                     except_bind
                       ~f:(fun acc_o ->
                           if is_equal @$ Id.compare i_actual i_expected then
                             let ec = ExprContext.insert ec i t_arg in
                             let t_e =
                               typecheck_exp
                                 ec
                                 tc
                                 vc
                                 e
                             in
                             except_bind
                               ~f:(fun t ->
                                   begin match acc_o with
                                     | None -> Left (Some t)
                                     | Some acc ->
                                       except_bind
                                         ~f:(fun b ->
                                             if b then
                                               Left (Some acc)
                                             else
                                               Right
                                                 ("inconsistent return types: "
                                                  ^ (Type.show acc)
                                                  ^ " and "
                                                  ^ (Type.show t)))
                                         (type_equiv tc acc t)
                                   end)
                               t_e
                           else
                             Right
                               ("Variant mismatch with "
                                ^ i_actual
                                ^ " and "
                                ^ i_expected))
                       acc_o_e)
                       ~init:(Left None)
                       merged_ordered_actual_expected))
        merged_ordered_actual_expected_e
    | Fix (i,t,e) ->
      let ec = ExprContext.insert ec i t in
      typecheck_exp ec tc vc e
    | Tuple es ->
      let ts_e =
        List.fold_right
          ~f:(fun e acc_e ->
              except_bind
                ~f:(fun acc ->
                    except_map
                      ~f:(fun t -> t::acc)
                      (typecheck_simple e))
                acc_e)
          ~init:(Left [])
          es
      in
      except_map
        ~f:Type.tuple
        ts_e
    | Proj (i,e) ->
      let t_e = typecheck_simple e in
      let t_e = except_bind ~f:(concretify tc) t_e in
      let ts_e =
        except_bind
          ~f:(fun t ->
              option_to_except
                ~f:(fun () -> "projection on non-tuple")
                (Type.destruct_tuple t))
          t_e
      in
      except_bind
        ~f:(fun ts ->
            option_to_except
              ~f:(fun () -> "projection of invalid component")
              (List.nth ts (i-1)))
        ts_e
  end

let typecheck_formula
    (ec:ExprContext.t)
    (tc:TypeContext.t)
    (vc:VariantContext.t)
    ((foralls,e):UniversalFormula.t)
  : Type.t list except =
  let (ec,ts) =
    List.fold_left
      ~f:(fun (ec,ts) (i,t) ->
          (ExprContext.insert ec i t,t::ts))
      ~init:(ec,[])
      foralls
  in
  let uf_type =
    typecheck_exp
      ec
      tc
      vc
      e
  in
  except_bind
    ~f:(fun t ->
        let equiv_e = type_equiv tc t (Type.mk_var "bool") in
        except_bind
          ~f:(fun b ->
              if b then
                Left ts
              else
                Right "universal formula was not a proposition")
          equiv_e)
    uf_type
