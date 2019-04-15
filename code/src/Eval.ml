open MyStdlib
open Lang

let rec evaluate
    (e:Expr.t)
  : Value.t =
  begin match e with
    | Var i -> failwith ("unbound variable " ^ i)
    | App (e1,e2) ->
      let e1 = Value.to_exp @$ evaluate e1 in
      let ((i,_),e1) = Expr.destruct_func_exn e1 in
      evaluate @$ Expr.replace i e2 e1
    | Func (a,e) -> Value.mk_func a e
    | Ctor (i,e) -> Value.mk_ctor i (evaluate e)
    | Match (e,i,branches) ->
      let (choice,v) = Value.destruct_ctor_exn (evaluate e) in
      let branch_o =
        List.Assoc.find
          ~equal:(is_equal %% Id.compare)
          branches
          choice
      in
      let branch =
        begin match branch_o with
          | None ->
            failwith ("constructor " ^ choice ^ " not matched")
          | Some b -> b
        end
      in
      evaluate @$ Expr.replace i (Value.to_exp v) branch
    | Fix (i,_,e') ->
      evaluate @$ Expr.replace i e e'
    | Tuple es ->
      Value.mk_tuple (List.map ~f:evaluate es)
    | Proj (i,e) ->
      let vs = Value.destruct_tuple_exn @$ evaluate e in
      List.nth_exn vs i
  end


let evaluate_with_holes
    ~eval_context:(i_e:(Id.t * Expr.t) list)
    (e:Expr.t)
  : Value.t =
  let e = Expr.replace_holes ~i_e e in
  evaluate e
