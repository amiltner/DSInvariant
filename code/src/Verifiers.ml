open MyStdlib
open Utils
open Lang

module type Verifier =
sig
  val implication_counter_example :
    ec:ExprContext.t ->
    tc:TypeContext.t ->
    vc:VariantContext.t ->
    i_e:(Id.t * Expr.t) list ->
    pre:Expr.t ->
    eval:Expr.t ->
    post:UniversalFormula.t ->
    (Expr.t list) option

  val true_on_examples :
    examples:Expr.t list ->
    eval:Expr.t ->
    post:Expr.t ->
    Expr.t option

  val synth :
    examples:Expr.t list ->
    eval:Expr.t ->
    post:Expr.t ->
    Expr.t option
end


module QuickCheckVerifier =
struct
  let true_val : Value.t = (Value.ctor "True" (Value.tuple []))

  let rec generator_of_type
      (tc:TypeContext.t)
      (t:Type.t)
    : Expr.t QC.g =
    let generator_of_type_simple = generator_of_type tc in
    fun i ->
      begin match t with
        | Var i ->
          generator_of_type_simple (TypeContext.lookup_exn tc i)
        | Arr _ ->
          failwith "Will do if necessary..."
        | Tuple ts ->
          QC.map
            ~f:Expr.tuple
            (fun i -> (QC.product (List.map ~f:generator_of_type_simple ts)) i)
        | Mu (v,t) ->
          let tc = TypeContext.insert tc v t in
          generator_of_type tc t
        | Variant options ->
          let options_generators =
            List.map
              ~f:(fun (i,t) ->
                  let g = generator_of_type_simple t in
                  let g = QC.map ~f:(Expr.ctor i) g in
                  QC.subtract_size g 1)
              options
          in
          QC.choice options_generators
      end
        i

  let rec contains_any
      (tc:TypeContext.t)
      (desired_t:Type.t)
      (t:Type.t)
    : bool =
    let contains_any_simple = contains_any tc desired_t in
    if is_equal (Type.compare t desired_t) then
      true
    else
      begin match t with
        | Var v ->
          begin match TypeContext.lookup tc v with
            | Some t -> contains_any_simple t
            | None -> false
          end
        | Arr (t1,t2) ->
          contains_any_simple t1 || contains_any_simple t2
        | Tuple ts ->
          List.exists ~f:contains_any_simple ts
        | Mu (i,t) ->
          let tc = TypeContext.insert tc i t in
          contains_any tc desired_t t
        | Variant branches ->
          List.exists ~f:contains_any_simple (List.map ~f:snd branches)
      end

  let rec extract_typed_subcomponents
      (tc:TypeContext.t)
      (desired_t:Type.t)
      (t:Type.t)
      (v:Value.t)
    : Value.t list =
    let extract_typed_subcomponents_simple = extract_typed_subcomponents tc desired_t in
    if is_equal (Type.compare t desired_t) then
      [v]
    else
      begin match (t,v) with
        | (Tuple ts, Tuple vs) ->
          List.concat_map
            ~f:(fun (t,v) -> extract_typed_subcomponents_simple t v)
            (List.zip_exn ts vs)
        | (Variant branches, Ctor (c,v)) ->
          let t =
            List.Assoc.find_exn
              ~equal:(is_equal %% String.compare)
              branches
              c
          in
          extract_typed_subcomponents_simple t v
        | (Var i, _) ->
          begin match TypeContext.lookup tc i with
            | None -> []
            | Some t -> extract_typed_subcomponents_simple t v
          end
        | (Mu (i,t), _) ->
          let tc = TypeContext.insert tc i t in
          extract_typed_subcomponents tc desired_t t v
        | (Arr _, _) -> failwith "arrows not currently supported"
        | _ -> failwith "Something went wrong"
      end

  let rec extract_args
      (t:Type.t)
    : Type.t list * Type.t =
    begin match t with
      | Arr (t1,t2) ->
        let (ts,tres) = extract_args t2 in
        (t1::ts,tres)
      | _ -> ([],t)
    end

  let implication_counter_example
      ~ec:(ec:ExprContext.t)
      ~tc:(tc:TypeContext.t)
      ~vc:(vc:VariantContext.t)
      ~i_e:(i_e:(Id.t * Expr.t) list)
      ~pre:(pre:Expr.t)
      ~eval:(eval:Expr.t)
      ~post:((post_quants,post_expr):UniversalFormula.t)
    : Expr.t list option =
    let desired_t = Type.mk_var "t" in
    let num_checks = 100 in
    let eval_t =
      either_left_exn @$
      Typecheck.typecheck_exp
        ec
        tc
        vc
        eval
    in
    let (args_t,result_t) = extract_args eval_t in
    if not @$ contains_any tc desired_t result_t then
      None
    else
      let pre_args_seqs =
        List.map
          ~f:(fun t ->
              let g = generator_of_type tc t in
              let seq = QC.g_to_seq g in
              if is_equal (Type.compare desired_t t) then
                Sequence.filter
                  ~f:(fun e ->
                      let pre_e_app =
                        Expr.app
                          pre
                          e
                      in
                      let v = Eval.evaluate_with_holes ~i_e pre_e_app in
                      is_equal (Value.compare v (Value.ctor "True" (Value.tuple []))))
                  seq
              else
                seq)
          args_t
      in
      let result_list =
        fold_until_completion
          ~f:(fun (resultant,i,seqs) ->
              if i > num_checks then
                Right resultant
              else
                let (args,seqs) =
                  List.fold_right
                    ~f:(fun seq (exps_names,uf_types_seqs) ->
                        let (exp_name,seq) = Option.value_exn (Sequence.next seq) in
                        (exp_name::exps_names,seq::uf_types_seqs))
                    ~init:([],[])
                    seqs
                in
                let res =
                  Eval.evaluate_with_holes ~i_e @$
                  List.fold_left
                    ~f:Expr.app
                    ~init:eval
                    args
                in
                let split_res =
                  extract_typed_subcomponents
                    tc
                    desired_t
                    result_t
                    res
                in
                let split_res_exps = List.map ~f:Value.to_exp split_res in
                let i = i + List.length split_res in
                Left (split_res_exps@resultant,i,seqs))
          ([],0,pre_args_seqs)
      in
      let result_gen = QC.of_list result_list in
      let uf_types_seqs
        : (string * Expr.t) Sequence.t list =
        List.map
          ~f:(fun (i,t) ->
              let gen =
                if is_equal (Type.compare (Type.mk_var "t") t) then
                  result_gen
                else
                  generator_of_type tc t
              in
              let seq = QC.g_to_seq gen in
              Sequence.map
                ~f:(fun e -> (i,e))
                seq)
          post_quants
      in
      let ce_option =
        fold_until_completion
          ~f:(fun (uf_types_seqs,i) ->
              if i = 100 then
                Right None
              else
                let (exps_names,uf_types_seqs) =
                  List.fold_right
                    ~f:(fun seq (exps_names,uf_types_seqs) ->
                        let (exp_name,seq) = Option.value_exn (Sequence.next seq) in
                        (exp_name::exps_names,seq::uf_types_seqs))
                    ~init:([],[])
                    uf_types_seqs
                in
                let post_held =
                  is_equal @$
                  Value.compare
                    true_val
                    (Eval.evaluate_with_holes ~i_e:(i_e@exps_names) post_expr)
                in
                if post_held then
                  Left (uf_types_seqs,i+1)
                else
                  let relevant =
                    List.filter_map
                      ~f:(fun (_,e) ->
                          (*if is_equal @$ Type.compare desired_t t then*)
                            Some e
                          (*else
                            None*))
                      exps_names
                  in
                  Right (Some relevant))
          (uf_types_seqs,0)
      in
      ce_option

let true_on_examples
    ~examples:(_:Expr.t list)
    ~eval:(_:Expr.t)
    ~post:(_:Expr.t)
  : Expr.t option =
  failwith "TODO"

  let simplify
      (e:Expr.t)
    : Expr.t =
    e

  let substitute
      (e:Expr.t)
      (_:Expr.t list)
      (_:Expr.t list)
    : Expr.t =
    e

  let synth
      ~examples:(_:Expr.t list)
      ~eval:(_:Expr.t)
      ~post:(_:Expr.t)
    : Expr.t option =
    failwith "not yet"
end

let quickcheck_verifier = (module QuickCheckVerifier : Verifier)
