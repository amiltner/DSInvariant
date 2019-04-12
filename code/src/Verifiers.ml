open MyStdlib
open Utils
open Lang

module type Verifier =
sig
  val implication_counter_example :
    problem:problem ->
    pre:Expr.t ->
    eval:Expr.t ->
    post:UniversalFormula.t ->
    (Value.t list) option

  val true_on_examples :
    problem:problem ->
    examples:Value.t list ->
    eval:Expr.t ->
    post:UniversalFormula.t ->
    Value.t option

  val synth :
    problem:problem ->
    testbed:TestBed.t ->
    Expr.t option
end


module QuickCheckVerifier =
struct
  let true_val : Value.t = (Value.mk_ctor "True" (Value.mk_tuple []))

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
            ~f:Expr.mk_tuple
            (fun i -> (QC.product (List.map ~f:generator_of_type_simple ts)) i)
        | Mu (v,t) ->
          let tc = TypeContext.insert tc v t in
          generator_of_type tc t
        | Variant options ->
          let options_generators =
            List.map
              ~f:(fun (i,t) ->
                  let g = generator_of_type_simple t in
                  let g = QC.map ~f:(Expr.mk_ctor i) g in
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
      ~problem:(problem:problem)
      ~pre:(pre:Expr.t)
      ~eval:(eval:Expr.t)
      ~post:((post_quants,post_expr):UniversalFormula.t)
    : Value.t list option =
    if Expr.is_func ~func_internals:Expr.mk_false_exp pre then
      None
    else
      let desired_t = Type.mk_var "t" in
      let num_checks = 100 in
      let eval_t =
        Typecheck.typecheck_exp
          problem.ec
          problem.tc
          problem.vc
          eval
      in
      let (args_t,result_t) = extract_args eval_t in
      if not @$ contains_any problem.tc desired_t result_t then
        None
      else
        let pre_args_seqs =
          List.map
            ~f:(fun t ->
                let g = generator_of_type problem.tc t in
                let seq = QC.g_to_seq g in
                if is_equal (Type.compare desired_t t) then
                  Sequence.filter
                    ~f:(fun e ->
                        let pre_e_app =
                          Expr.mk_app
                            pre
                            e
                        in
                        let v = Eval.evaluate_with_holes ~eval_context:problem.eval_context pre_e_app in
                        is_equal (Value.compare v (Value.mk_ctor "True" (Value.mk_tuple []))))
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
                    Eval.evaluate_with_holes ~eval_context:problem.eval_context @$
                    List.fold_left
                      ~f:Expr.mk_app
                      ~init:eval
                      args
                  in
                  let split_res =
                    extract_typed_subcomponents
                      problem.tc
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
          : (Expr.t * string * Type.t) Sequence.t list =
          List.map
            ~f:(fun (i,t) ->
                let gen =
                  if is_equal (Type.compare (Type.mk_var "t") t) then
                    result_gen
                  else
                    generator_of_type problem.tc t
                in
                let seq = QC.g_to_seq gen in
                Sequence.map
                  ~f:(fun e -> (e,i,t))
                  seq)
            post_quants
        in
        let ce_option =
          fold_until_completion
            ~f:(fun (uf_types_seqs,i) ->
                if i = 100 then
                  Right None
                else
                  let (exps_names_types,uf_types_seqs) =
                    List.fold_right
                      ~f:(fun seq (exps_names,uf_types_seqs) ->
                          let (exp_name,seq) = Option.value_exn (Sequence.next seq) in
                          (exp_name::exps_names,seq::uf_types_seqs))
                      ~init:([],[])
                      uf_types_seqs
                  in
                  let (names_exps,exps_types) =
                    List.unzip @$
                    List.map
                      ~f:(fun (exp,name,typ) -> ((name,exp),(exp,typ)))
                      exps_names_types
                  in
                  let post_held =
                    is_equal @$
                    Value.compare
                      true_val
                      (Eval.evaluate_with_holes ~eval_context:(problem.eval_context@names_exps) post_expr)
                  in
                  if post_held then
                    Left (uf_types_seqs,i+1)
                  else
                    let relevant =
                      List.filter_map
                        ~f:(fun (e,t) ->
                            if is_equal @$ Type.compare desired_t t then
                              Some e
                            else
                              None)
                        exps_types
                    in
                    Right (Some relevant))
            (uf_types_seqs,0)
        in
        Option.map
          ~f:(List.map ~f:Value.from_exp_exn)
          ce_option

  let true_on_examples
      ~problem:(_:problem)
      ~examples:(_:Value.t list)
      ~eval:(_:Expr.t)
      ~post:(_:UniversalFormula.t)
    : Value.t option =
    failwith "TODO"

  let synth
      ~(problem:problem)
      ~(testbed:TestBed.t)
    : Expr.t option =
    print_endline @$ TestBed.show testbed;
    Myth.Consts.verbose_mode := true;
    let pos_examples = List.map ~f:(fun (v,_) -> (Value.to_exp v,Expr.mk_true_exp)) testbed.pos_tests in
    let neg_examples = List.map ~f:(fun (v,_) -> (Value.to_exp v,Expr.mk_false_exp)) testbed.neg_tests in
    let examples = pos_examples@neg_examples in
    print_endline (string_of_list (string_of_pair Expr.show Expr.show) examples);
    if (List.length examples = 0) then
      Some (Expr.mk_constant_true_func (Type.mk_var "t"))
    else
      let (decls,examples,t) = DSToMyth.convert_problem_examples_type_to_myth problem examples in
      let (sigma,gamma) =
        Myth.Typecheck.Typecheck.check_decls
          Myth.Sigma.Sigma.empty
          Myth.Gamma.Gamma.empty
          decls
      in
      let env = Myth.Eval.gen_init_env decls in
      let w = Myth.Eval.gen_init_world env [Myth.Lang.EPFun examples] in
      Option.map
        ~f:MythToDS.convert_expr
        (Myth.Synth.synthesize
           sigma
           env
           (Myth.Rtree.create_rtree
              sigma
              gamma
              env
              (TArr (t,TBase "bool")) w 0))
end

let quickcheck_verifier = (module QuickCheckVerifier : Verifier)
