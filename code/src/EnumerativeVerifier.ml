open MyStdlib
open Utils
open Lang

module T : Verifier.t =
struct
  let _NUM_CHECKS_ = 2048

  let true_val : Value.t = (Value.mk_ctor "True" (Value.mk_tuple []))

  module TypeToGeneratorDict =
  struct
    module Generators =
    struct
      type t = Expr.t Sequence.t
      [@@deriving ord]

      let hash _ = failwith "dont"
      let hash_fold_t _ = failwith "don't"
      let pp _ = failwith "don't"
      let show _ = failwith "don't"
    end
    module D = DictOf(Type)(Generators)

    type t = D.t * (Type.t -> Expr.t Sequence.t)

    let get_val
        ((d,fs):t)
        (t:Type.t)
      : t * Expr.t =
      begin match D.lookup d t with
        | None ->
          let g = fs t in
          let (v,g) = Option.value_exn (Sequence.next g) in
          let d = D.insert d t g in
          ((d,fs),v)
        | Some g ->
          let (v,g) = Option.value_exn (Sequence.next g) in
          let d = D.insert d t g in
          ((d,fs),v)
      end

    let create
        (fs:(Type.t -> Expr.t Sequence.t))
      : t =
      (D.empty,fs)
  end

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

  module TypeSet = SetOf(Type)

  let contains_any
      (tc:TypeContext.t)
      (desired_t:Type.t)
      (t:Type.t)
    : bool =
    let rec contains_any
        (tc:TypeContext.t)
        (desired_t:Type.t)
        (checked:TypeSet.t)
        (t:Type.t)
      : bool =
      if TypeSet.member checked t then
        false
      else if is_equal (Type.compare t desired_t) then
        true
      else
        let checked = TypeSet.insert t checked in
        let contains_any_simple = contains_any tc desired_t checked in
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
            contains_any tc desired_t checked t
          | Variant branches ->
            List.exists ~f:contains_any_simple (List.map ~f:snd branches)
        end
    in
    contains_any tc desired_t TypeSet.empty t

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

  let make_evaluators_upto_size
      ~(size:int)
      ~(problem:problem)
      ~(eval:Expr.t)
      ~(eval_t:Type.t)
      ~(gen:TypeToGeneratorDict.t)
    : ((Expr.t * Type.t) list * Value.t) list =
    (* Eagerly returning all expressions till size "size" ... *)
    raise (Exceptions.Internal_Exn "NOT IMPLEMENTED")
    (* let (args_t,_) = extract_args eval_t in
    let (args,d) =
      List.fold_right
        ~f:(fun t (args,d) ->
            let (d,e) = TypeToGeneratorDict.get_val d t in
            ((e,t)::args,d))
        ~init:([],gen)
        args_t
    in
    (args
    ,Eval.evaluate_with_holes
        ~eval_context:problem.eval_context
        (List.fold_left
           ~f:(fun acc (e,_) -> Expr.mk_app acc e)
           ~init:eval
           args)
    ,d) *)

  let equiv_false
      ~(problem:problem)
      ~cond:(cond:Expr.t)
    : bool =
    let cond_t = Type.mk_arr Type.mk_t_var Type.mk_bool_var in
    let generators
        (t:Type.t)
      : Expr.t Sequence.t =
       let g = generator_of_type problem.tc t in
       QC.g_to_seq g
     in
     let gen = TypeToGeneratorDict.create generators
      in try List.fold (make_evaluators_upto_size ~size:_NUM_CHECKS_
                                                  ~problem
                                                  ~eval:cond
                                                  ~eval_t:cond_t
                                                  ~gen)
                        ~init:true
                        ~f:(fun _ (_,res) -> if is_equal @$ Value.compare res Value.mk_true
                                             then true else raise Caml.Exit)
         with Caml.Exit -> false
     (* fold_until_completion
       ~f:(fun (i,gen) ->
           if i > num_checks then
             Right true
           else
             let (_,res,gen) =
               make_random_evaluator
                 ~problem
                 ~eval:cond
                 ~eval_t:cond_t
                 ~gen
             in
             if is_equal @$ Value.compare res Value.mk_true then
               Right false
             else
               Left (i+1,gen))
       (0,gen) *)

  let implication_counter_example
      ~problem:(problem:problem)
      ~pre:(pre:Expr.t)
      ~eval:(eval:Expr.t)
      ~(eval_t:Type.t)
      ~post:((post_quants,post_expr):UniversalFormula.t)
    : Value.t list option =
    let desired_t = Type.mk_var "t" in
    if equiv_false ~problem ~cond:pre
    && List.exists
         ~f:(fun (_,t) -> is_equal @$ Type.compare t desired_t)
         post_quants
    then
      begin
        print_endline "SKIP OUT FAST";
        None
      end
    else
      let num_checks = _NUM_CHECKS_ in
      let (_,result_t) = extract_args eval_t in
      if not @$ contains_any problem.tc desired_t result_t then
        (None)
      else
        (let generators
            (t:Type.t)
          : Expr.t Sequence.t =
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
            seq
         in
         let gen = TypeToGeneratorDict.create generators in
        let result_list =
          fold_until_completion
            ~f:(fun (resultant,i,gen) ->
                if i > num_checks then
                  Right resultant
                else
                  let (args,res,gen) =
                    make_random_evaluator
                      ~problem
                      ~eval
                      ~eval_t
                      ~gen
                  in
                  let split_res =
                    extract_typed_subcomponents
                      problem.tc
                      desired_t
                      result_t
                      res
                  in
                  let arged_split_res =
                    List.map
                      ~f:(fun r -> (args,Value.to_exp r))
                      split_res
                  in
                  let i = i + List.length split_res in
                  Left (arged_split_res@resultant,i,gen))
            ([],0,gen)
        in
        let result_gen = QC.of_list result_list in
        let uf_types_seqs
          : ((Expr.t * Type.t) list * Expr.t * string * Type.t) Sequence.t list =
          List.map
            ~f:(fun (i,t) ->
                let gen =
                  if is_equal (Type.compare (Type.mk_var "t") t) then
                    result_gen
                  else
                    QC.map ~f:(fun g -> ([],g)) (generator_of_type problem.tc t)
                in
                let seq = QC.g_to_seq gen in
                Sequence.map
                  ~f:(fun (ts,e) -> (ts,e,i,t))
                  seq)
            post_quants
        in
        let ce_option =
          fold_until_completion
            ~f:(fun (uf_types_seqs,i) ->
                if i = 100 then
                  Right None
                else
                  let (args_exps_names_types,uf_types_seqs) =
                    List.fold_right
                      ~f:(fun seq (exps_names,uf_types_seqs) ->
                          let (exp_name,seq) = Option.value_exn (Sequence.next seq) in
                          (exp_name::exps_names,seq::uf_types_seqs))
                      ~init:([],[])
                      uf_types_seqs
                  in
                  let (args_l,names_exps) =
                    List.unzip @$
                    List.map
                      ~f:(fun (args,exp,name,_) -> (args,(name,exp)))
                      args_exps_names_types
                  in
                  let args = List.concat args_l in
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
                        args
                    in
                    Right (Some relevant))
            (uf_types_seqs,0)
        in
        Option.map
          ~f:(List.map ~f:Value.from_exp_exn)
          ce_option)

  let true_on_examples
      ~(problem:problem)
      ~(examples:Value.t list)
      ~(eval:Expr.t)
      ~(eval_t:Type.t)
      ~post:((post_quants,post_expr):UniversalFormula.t)
    : Value.t option =
    let num_checks = _NUM_CHECKS_ in
    let desired_t = Type.mk_var "t" in
    let (args_t,result_t) = extract_args eval_t in
    if (List.length examples = 0
        && List.mem ~equal:(is_equal %% Type.compare) args_t desired_t)
    || not (contains_any problem.tc desired_t result_t) then
      None
    else
      let generators
          (t:Type.t)
        : Expr.t Sequence.t =
        if is_equal @$ Type.compare t desired_t then
          QC.g_to_seq @$ QC.of_list (List.map ~f:Value.to_exp examples)
        else
          QC.g_to_seq @$ generator_of_type problem.tc t
      in
      let gen = TypeToGeneratorDict.create generators in
      let result_list =
        fold_until_completion
          ~f:(fun (resultant,i,gen) ->
              if i > num_checks then
                Right resultant
              else
                let (_,res,gen) = make_random_evaluator ~problem ~eval ~eval_t ~gen in
                let split_res =
                  extract_typed_subcomponents
                    problem.tc
                    desired_t
                    result_t
                    res
                in
                let split_res_exps = List.map ~f:Value.to_exp split_res in
                let i = i + List.length split_res in
                Left (split_res_exps@resultant,i,gen))
          ([],0,gen)
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
      Option.map ~f:List.hd_exn @$
      Option.map
        ~f:(List.map ~f:Value.from_exp_exn)
        ce_option

  let convert_foldable_to_full
      (tc:TypeContext.t)
      (fold_completion:Type.t)
    : Expr.t =
    let convert_internal_id = "convert'" in
    let convert_internal_exp = Expr.mk_var convert_internal_id in
    let rec convert_foldable_internal
        (i:Id.t)
        (t:Type.t)
        (incoming_exp:Expr.t)
      : Expr.t =
      begin match t with
        | Var i' ->
          if is_equal @$ Id.compare i i' then
            Expr.mk_app
              convert_internal_exp
              incoming_exp
          else
            incoming_exp
        | Tuple ts ->
          Expr.mk_tuple
            (List.mapi
               ~f:(fun num t ->
                   convert_foldable_internal
                     i
                     t
                     (Expr.mk_proj num incoming_exp))
               ts)
        | Variant branches ->
          Expr.mk_match
            incoming_exp
            "x"
            (List.map
               ~f:(fun (b,t) ->
                   (b,Expr.mk_ctor
                      (Id.mk_prime b)
                      (convert_foldable_internal
                         i
                         t
                         (Expr.mk_var "x"))))
               branches)
        | Mu _
        | Arr _ ->
          incoming_exp
      end
    in
    let t = TypeContext.lookup_exn tc "t" in
    let tv = Type.destruct_id_exn t in
    let t = TypeContext.lookup_exn tc tv in
    let ito = Type.destruct_mu t in
    let t' = Type.mk_var (Id.mk_prime "t") in
    begin match ito with
      | None ->
        Expr.mk_func
          ("x",Type.mk_arr t' t')
          (Expr.mk_var "x")
      | Some (i,t_internal) ->
        Expr.mk_func
          ("f",Type.mk_arr
             t'
             fold_completion)
          (Expr.mk_fix
             convert_internal_id
             (Type.mk_arr Type.mk_t_var fold_completion)
             (Expr.mk_func
                ("x",Type.mk_t_var)
                (Expr.mk_app
                   (Expr.mk_var "f")
                   (convert_foldable_internal
                      i
                      t_internal
                      (Expr.mk_var "x")))))
    end

  let get_foldable_t
      (tc:TypeContext.t)
      (fold_completion:Type.t)
    : Type.t =
    let rec type_to_folded_type_internal
        (i:Id.t)
        (t:Type.t)
      : Type.t =
      begin match t with
        | Var i' ->
          if is_equal @$ Id.compare i i' then
            fold_completion
          else
            t
        | Tuple ts ->
          Tuple (List.map ~f:(type_to_folded_type_internal i) ts)
        | Variant branches ->
          Variant
            (List.map
               ~f:(fun (b,t) ->
                   (Id.mk_prime b
                   ,type_to_folded_type_internal i t))
               branches)
        | Arr _ | Mu _ -> t
      end
    in
    let t = TypeContext.lookup_exn tc "t" in
    let tv = Type.destruct_id_exn t in
    let t = TypeContext.lookup_exn tc tv in
    let ito = Type.destruct_mu t in
    begin match ito with
      | None -> t
      | Some (i,t) ->
        type_to_folded_type_internal i t
    end

  let synth
      ~(problem:problem)
      ~(testbed:TestBed.t)
    : Expr.t option =
    let acc_type = Type.mk_var "natoption" in
    let end_type = Type.mk_tuple [Type.mk_bool_var;acc_type] in
    let pos_examples = List.map ~f:(fun (v,_) -> (Value.to_exp v,Expr.mk_true_exp)) testbed.pos_tests in
    let neg_examples = List.map ~f:(fun (v,_) -> (Value.to_exp v,Expr.mk_false_exp)) testbed.neg_tests in
    let examples = pos_examples@neg_examples in
    let (decls,_,_,_) =
      DSToMyth.convert_problem_examples_type_to_myth
        problem
        examples
        None
    in
    let (_,gamma) =
      Myth_folds.Typecheck.Typecheck.check_decls
        Myth_folds.Sigma.Sigma.empty
        Myth_folds.Gamma.Gamma.empty
        decls
    in
    let foldable_t = get_foldable_t problem.tc end_type in
    let fold_creater =
      convert_foldable_to_full
        problem.tc
        end_type
    in
    let (ds,mi,ms,uf) = problem.unprocessed in
    let unprocessed =
      (ds
      ,mi@[Declaration.type_dec (Id.mk_prime "t") foldable_t
          ;Declaration.expr_dec "convert" fold_creater]
      ,ms
      ,uf)
    in
    let problem = ProcessFile.process_full_problem unprocessed in
    if (List.length examples = 0) then
      Some (Expr.mk_constant_true_func (Type.mk_var "t"))
    else
      let (decls,myth_examples,t,end_type_myth) =
        DSToMyth.convert_problem_examples_type_to_myth
          problem
          examples
          (Some end_type)
      in
      let (sigma,_) =
        Myth_folds.Typecheck.Typecheck.check_decls
          Myth_folds.Sigma.Sigma.empty
          Myth_folds.Gamma.Gamma.empty
          decls
      in
      let env = Myth_folds.Eval.gen_init_env decls in
      let desired_t =
        Type.mk_arr
          (Type.mk_var "t")
          (Type.mk_var "bool")
      in
      let correct_check =
        fun e ->
              (*print_endline @$ Myth_folds.Pp.pp_exp e;*)
              let evaler = Myth_folds.Lang.EApp (EVar "convert", e) in
              let corrects =
                List.map
                  ~f:(fun (e1,e2) ->
                      try
                        let ans =
                          Myth_folds.Eval.eval
                            env
                            (Myth_folds.Lang.EProj
                               (1
                               ,Myth_folds.Lang.EApp(evaler,e1)))
                        in
                        if ans = Myth_folds.Eval.eval env e2 then
                          1
                        else
                          0
                      with
                        Myth_folds.Eval.Eval_error _ -> 0)
                  myth_examples
              in
              let total_correct = List.fold_left ~f:(+) ~init:0 corrects in
              let total = List.length corrects in
              (*print_endline (Float.to_string ((Float.of_int total_correct) /. (Float.of_int total)));*)
              (Float.of_int total_correct) /. (Float.of_int total)
      in
      let _ =
        fun e ->
          let evaler = Myth_folds.Lang.EApp (EVar "convert", e) in
          List.map
            ~f:(fun (input,_) ->
                try
                  Left
                    (Myth_folds.Eval.eval
                       env
                       (Myth_folds.Lang.EProj
                          (1
                          ,Myth_folds.Lang.EApp(evaler,input))))
                with
                  Myth_folds.Eval.Eval_error _ -> Right ())
            myth_examples
      in
      let _ = compare_list ~cmp:(compare_either Myth_folds.Lang.compare_exp Unit.compare) in
      Option.map
        ~f:(fun me ->
            let e = MythToDS.convert_expr me in
            let e = Typecheck.align_types desired_t e in
            let full_e = Expr.mk_app fold_creater e in
            Expr.mk_func
              ("x",Type.mk_t_var)
              (Expr.mk_proj 0
                 (Expr.mk_app full_e (Expr.mk_var "x"))))
        (Myth_folds.Synth.synthesize
           sigma
           env
           (Myth_folds.Rtree.create_rtree
              sigma
              gamma
              env
              (TArr (t,end_type_myth))
              0)
           correct_check
           )
end