(* open Async *)
open Core

open Utils
open Lang

(* module Worker = struct
  module T = struct
    type w_input = problem * TestBed.t * Type.t [@@deriving bin_io]
    type w_output = Expr.t option [@@deriving bin_io]

    type 'worker functions = {
      synth : ('worker, w_input, w_output) Rpc_parallel.Function.t
    }

    module Worker_state = struct
      type init_arg = unit [@@deriving bin_io]
      type t = unit
    end

    module Connection_state = struct
      type init_arg = unit [@@deriving bin_io]
      type t = unit
    end

    module Functions (C : Rpc_parallel.Creator
                          with type worker_state := Worker_state.t
                          and type connection_state := Connection_state.t) =
    struct
      let print_impl ~worker_state:() ~conn_state:() string =
        printf "%s\n" string;
        return ()
      ;;

      let print =
        C.create_rpc ~f:print_impl ~bin_input:String.bin_t ~bin_output:Unit.bin_t ()
      ;;

      let functions = { print }
      let init_worker_state () = Deferred.unit
      let init_connection_state ~connection:_ ~worker_state:_ = return
    end
  end

  include Rpc_parallel.Make (T)
end *)

module T : Synthesizer.t = struct
  let synth_core
      ~(problem:problem)
      ~(testbed:TestBed.t)
      ~(accumulator:Type.t)
    : Expr.t option =
    let end_type = Type.mk_tuple [Type.mk_bool_var ; accumulator] in
    let pos_examples = List.map ~f:(fun v -> (Value.to_exp v, Expr.mk_true_exp)) testbed.pos_tests in
    let neg_examples = List.map ~f:(fun v -> (Value.to_exp v, Expr.mk_false_exp)) testbed.neg_tests in
    let examples = pos_examples @ neg_examples in
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
    let (ds,mi,ms,uf,acc) = problem.unprocessed in
    let unprocessed =
      (ds
      ,mi @ [ Declaration.type_dec (Id.mk_prime "t") foldable_t
            ; Declaration.expr_dec "convert" fold_creater ]
      ,ms
      ,uf
      ,acc)
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
      let env = Myth_folds.Sigma.Sigma.add_ctors_env env sigma in
      let gamma = Myth_folds.Gamma.Gamma.add_ctors gamma sigma in
      let desired_t =
        Type.mk_arr
          (Type.mk_var "t")
          (Type.mk_var "bool")
      in
      let tests_outputs : Myth_folds.Lang.exp Myth_folds.Rtree.tests_outputs =
        List.map
          ~f:(fun (input,expected_output) ->
              (input
              ,expected_output
              ,(fun e ->
                 let evaler = Myth_folds.Lang.EApp (EVar "convert", e) in
                 let (output,is_real) =
                   try
                     let ans =
                       Myth_folds.Eval.eval
                         env
                         (Myth_folds.Lang.EApp(evaler,input))
                     in
                     (Some ans,true)
                   with
                   | Myth_folds.Eval.Eval_error _ -> (None,true)
                   | Myth_folds.Eval.Extr_error v -> (Some v,false)
                 in
                 let correct =
                   is_real &&
                   begin match output with
                     | None -> false
                     | Some (Myth_folds.Lang.VTuple vs) ->
                       let ans = Myth_folds.Eval.eval env expected_output in
                       ans = List.hd_exn vs
                     | _ -> false
                   end
                 in
                 Myth_folds.Rtree.ExistantLeaf (correct, output))))
          myth_examples
      in
      (*Some [(
                     let evaler = Myth_folds.Lang.EApp (EVar "convert", e) in
                     let (real_output,output) =
                       try
                         (true
                         ,Some (Myth_folds.Eval.eval
                                  env
                                  (Myth_folds.Lang.EApp(evaler,input))))
                       with
                         Myth_folds.Eval.Eval_error _ -> (true,None)
                       | Myth_folds.Eval.Extr_error v -> (false, Some v)
                     in
                     let correct =
                       real_output &&
                       begin match output with
                         | Some (Myth_folds.Lang.VTuple vs) ->
                           print_endline (Myth_folds.Pp.pp_value (Myth_folds.Lang.VTuple vs));
                           let expected_value = Myth_folds.Eval.eval env expected_output in
                           print_endline (Myth_folds.Pp.pp_value expected_value);
                           List.hd_exn vs = Myth_folds.Eval.eval env expected_output
                         | None -> false
                         | _ -> failwith "unexpected"
                       end
                     in
                     (output,correct)
                  )])
            )
          myth_examples
                  in*)
      (*let correct_check =
        List.map
          ~f:(fun (e1,e2) ->
              (e1,fun e ->
                let evaler = Myth_folds.Lang.EApp (EVar "convert", e) in
                try
                   let ans =
                     Myth_folds.Eval.eval
                       env
                       (Myth_folds.Lang.EProj
                          (1
                          ,Myth_folds.Lang.EApp(evaler,e1)))
                   in
                   ans = Myth_folds.Eval.eval env e2
                 with
                 | Myth_folds.Eval.Eval_error _ -> false
                ))
          myth_examples
          (*let total_correct = List.fold_left ~f:(+) ~init:0 corrects in
              let total = List.length corrects in
              (*print_endline (Float.to_string ((Float.of_int total_correct) /. (Float.of_int total)));*)
                (Float.of_int total_correct) /. (Float.of_int total)*)
        in*)
      (*let to_outputs =
        fun e ->
          let evaler = Myth_folds.Lang.EApp (EVar "convert", e) in
          Myth_folds.Rtree.Output.create
            [Some (List.map
                     ~f:(fun (input,_) ->
                         try
                           Some
                             (Myth_folds.Eval.eval
                                env
                                (Myth_folds.Lang.EApp(evaler,input)))
                         with
                           Myth_folds.Eval.Eval_error _ -> None
                         | Myth_folds.Eval.Extr_error v -> Some v)
                     myth_examples)]
        in*)
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
              0
              true)
           tests_outputs)

  let synth
      ~(problem:problem)
      ~(testbed:TestBed.t)
    : Expr.t option =
    match problem.accumulator with
    | Some accumulator -> synth_core ~problem ~testbed ~accumulator
    | None -> begin
      let config =
          Rpc_parallel.Map_reduce.Config.create
            ~local:4
            ~redirect_stderr:`Dev_null
            ~redirect_stdout:`Dev_null
            ()
       in ignore config
        ; raise (Exceptions.Internal_Exn "TODO")
    end
end