open MyStdlib
open Lang
open Typecheck

let extract_variants
    (t:Type.t)
  : (VariantContext.key * VariantContext.value) list =
  fst @$
  Type.fold
    ~base_f:(fun i -> ([],Type.mk_var i))
    ~arr_f:(fun (vs1,t1) (vs2,t2) -> (vs1@vs2,Type.mk_arr t1 t2))
    ~tuple_f:(fun vss_ts ->
        let (vss,ts) = List.unzip vss_ts in
        (List.concat vss, Type.tuple ts))
    ~mu_f:(fun _ vs -> vs)
    ~variant_f:(fun ids_vss_ts ->
        let (ids,vss_ts) = List.unzip ids_vss_ts in
        let (vss,ts) = List.unzip vss_ts in
        let ids_ts = List.zip_exn ids ts in
        let ids_map = List.map ~f:(fun id -> (id,ids_ts)) ids in
        (ids_map@(List.concat vss), Type.variant ids_ts))
    t

let process_decl_list
    (ec:ExprContext.t)
    (tc:TypeContext.t)
    (vc:VariantContext.t)
    (ds:Declaration.t list)
  : (ExprContext.t * TypeContext.t * VariantContext.t * (Id.t * Expr.t) list) except =
  except_map
    ~f:fst
    (List.fold_left
       ~f:(fun ec_tc_vc_e decl ->
           except_bind
             ~f:(fun ((new_ec,new_tc,new_vc,i_e),(ec,tc,vc)) ->
                 Declaration.fold
                   ~type_f:(fun i t ->
                       let all_variants = extract_variants t in
                       Left
                         ((new_ec
                          ,TypeContext.insert new_tc i t
                          ,List.fold_left
                              ~f:(fun vc (k,v) -> VariantContext.insert vc k v)
                              ~init:new_vc
                              all_variants
                          ,i_e)
                         ,(ec
                          ,TypeContext.insert tc i t
                          ,List.fold_left
                              ~f:(fun vc (k,v) -> VariantContext.insert vc k v)
                              ~init:vc
                              all_variants))
                     )
                   ~expr_f:(fun i e ->
                       except_map
                         ~f:(fun t ->
                             ((ExprContext.insert new_ec i t
                              ,new_tc
                              ,new_vc
                              ,(i,e)::i_e)
                             ,(ExprContext.insert ec i t
                              ,tc
                              ,vc)))
                         (typecheck_exp ec tc vc e))
                   decl)
             ec_tc_vc_e)
       ~init:(Left
                ((ExprContext.empty,TypeContext.empty,VariantContext.empty,[])
                ,(ec,tc,vc)))
       ds)

let process_module_sig
    (ec:ExprContext.t)
    ((_,ets):ModuleSpec.t)
  : ExprContext.t =
  List.fold_left
    ~f:(fun ec (i,t) ->
        ExprContext.insert
          ec
          i
          t)
    ~init:ec
    ets


let validate_module_satisfies_spec
    (full_tc:TypeContext.t)
    (ec:ExprContext.t)
    (tc:TypeContext.t)
    ((i,es):ModuleSpec.t)
  : bool except =
  List.fold_left
    ~f:(fun acc_e (i,t) ->
        except_bind
          ~f:(fun acc ->
              if not acc then
                Left acc
              else
                begin match ExprContext.lookup ec i with
                  | None -> Left false
                  | Some t' -> Typecheck.type_equiv full_tc t t'
                end)
          acc_e
      )
    ~init:(Left (Option.is_some @$ TypeContext.lookup tc i))
    es

let process_full_problem
    ((decs,modi,mods,uf):problem)
  : (Type.t
     * ExprContext.t
     * TypeContext.t
     * VariantContext.t
     * Type.t list
     * UniversalFormula.t
     * (Id.t * Expr.t) list) except =
  let ec_tc_vc_e =
    process_decl_list
      ExprContext.empty
      TypeContext.empty
      VariantContext.empty
      decs
  in
  let context_modonly_context_e =
    except_bind
      ~f:(fun (ec,tc,vc,i_e) ->
          except_map
            ~f:(fun ectcvc' ->
                let (ec',tc',vc',i_e') = ectcvc' in
                ((ec,tc,vc),(ec',tc',vc'),i_e'@i_e))
            (process_decl_list ec tc vc modi))
      ec_tc_vc_e
  in
  let validated_context_modonly_context_e =
    except_bind
      ~f:(fun ((ec,tc,vc),(m_ec,m_tc,m_vc),i_e) ->
          let full_tc =
            TypeContext.from_kvp_list
              (TypeContext.merge
                 ~combiner:(fun _ v -> v)
                 ~only_d1_fn:ident
                 ~only_d2_fn:ident
                 tc
                 m_tc)
          in
          let satisfies_e =
            validate_module_satisfies_spec
              full_tc
              m_ec
              m_tc
              mods
          in
          except_bind
            ~f:(fun b ->
                if (not b) then
                  Right "module doesn't satisfy spec"
                else
                  Left (((ec,tc,vc),(m_ec,m_tc,m_vc),i_e)))
            satisfies_e)
      context_modonly_context_e
  in
  let validated_context_modonly_context_uf_e =
    except_bind
      ~f:(fun ((ec,tc,vc),(m_ec,m_tc,m_vc),i_e) ->
          let ec_sig = process_module_sig ec mods in
          let ftl_e = typecheck_formula ec_sig tc vc uf in
          except_map
            ~f:(fun tl -> ((ec,tc,vc),(m_ec,m_tc,m_vc),tl,uf,i_e))
            ftl_e)
      validated_context_modonly_context_e
  in
  except_map
    ~f:(fun ((ec,tc,vc),(m_ec,m_tc,m_vc),tl,uf,i_e) ->
        let full_ec =
          TypeContext.from_kvp_list
            (ExprContext.merge
               ~combiner:(fun _ v -> v)
               ~only_d1_fn:ident
               ~only_d2_fn:ident
               ec
               m_ec)
        in
        let full_tc =
          TypeContext.from_kvp_list
            (TypeContext.merge
               ~combiner:(fun _ v -> v)
               ~only_d1_fn:ident
               ~only_d2_fn:ident
               tc
               m_tc)
        in
        let full_vc =
          VariantContext.from_kvp_list
            (VariantContext.merge
               ~combiner:(fun _ v -> v)
               ~only_d1_fn:ident
               ~only_d2_fn:ident
               vc
               m_vc)
        in
        let type_instantiation =
          TypeContext.lookup_exn
            full_tc
            (fst mods)
        in
        (type_instantiation,full_ec,full_tc,full_vc,tl,uf,i_e))
    validated_context_modonly_context_uf_e
