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
        (List.concat vss, Type.mk_tuple ts))
    ~mu_f:(fun _ vs -> vs)
    ~variant_f:(fun ids_vss_ts ->
        let (ids,vss_ts) = List.unzip ids_vss_ts in
        let (vss,ts) = List.unzip vss_ts in
        let ids_ts = List.zip_exn ids ts in
        let ids_map = List.map ~f:(fun id -> (id,ids_ts)) ids in
        (ids_map@(List.concat vss), Type.mk_variant ids_ts))
    t

let process_decl_list
    (ec:ExprContext.t)
    (tc:TypeContext.t)
    (vc:VariantContext.t)
    (ds:Declaration.t list)
  : (ExprContext.t * TypeContext.t * VariantContext.t * (Id.t * Expr.t) list) =
  fst
    (List.fold_left
       ~f:(fun ((new_ec,new_tc,new_vc,i_e),(ec,tc,vc)) decl ->
           Declaration.fold
             ~type_f:(fun i t ->
                 let all_variants = extract_variants t in
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
                 let t = typecheck_exp ec tc vc e in
                 ((ExprContext.insert new_ec i t
                  ,new_tc
                  ,new_vc
                  ,(i,e)::i_e)
                 ,(ExprContext.insert ec i t
                  ,tc
                  ,vc))
               )
             decl)
       ~init:(((ExprContext.empty,TypeContext.empty,VariantContext.empty,[])
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
  : bool =
  List.fold_left
    ~f:(fun acc (i,t) ->
            if not acc then
              acc
            else
              begin match ExprContext.lookup ec i with
                | None -> false
                | Some t' -> Typecheck.type_equiv full_tc t t'
              end)
    ~init:(Option.is_some @$ TypeContext.lookup tc i)
    es

let process_full_problem
    (unprocessed:unprocessed_problem)
  : problem =
  let (decs,modi,mods,uf,accumulator) = unprocessed in
  let (ec,tc,vc,i_e) =
    process_decl_list
      ExprContext.empty
      TypeContext.empty
      VariantContext.empty
      decs
  in
  let m_ec,m_tc,m_vc,i_e' = process_decl_list ec tc vc modi in
  let i_e = i_e'@i_e in
  let full_tc =
    TypeContext.from_kvp_list
      (TypeContext.merge
         ~combiner:(fun _ v -> v)
         ~only_d1_fn:ident
         ~only_d2_fn:ident
         tc
         m_tc)
  in
  let satisfies =
    validate_module_satisfies_spec
      full_tc
      m_ec
      m_tc
      mods
  in
  if not satisfies then
    failwith "module doesn't satisfy spec"
  else
    let module_vals =
      List.map
        ~f:(fun (i,t) ->
            (List.Assoc.find_exn
              ~equal:(is_equal %% Id.compare)
              i_e
              i
            ,t))
        (snd mods)
    in
    let ec_sig = process_module_sig ec mods in
    let _ = typecheck_formula ec_sig tc vc uf in
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
    let eval_context =
      (List.concat_map
         ~f:(fun cts ->
             List.map
               ~f:(fun (c,t) -> (c, Expr.mk_func ("i",t) (Expr.Ctor (c, Expr.mk_var "i"))))
               cts)
         (VariantContext.value_list full_vc))
      @ i_e
    in
    let partial_problem = make_problem
                            ~module_type:type_instantiation
                            ~ec:full_ec
                            ~tc:full_tc
                            ~vc:full_vc
                            ~mod_vals:module_vals
                            ~post:uf
                            ~eval_context
                            ~unprocessed
     in match accumulator with
        | None -> partial_problem ()
        | Some acc -> partial_problem ~accumulator:acc ()
