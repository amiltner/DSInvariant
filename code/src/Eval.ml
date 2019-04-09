open MyStdlib
open Lang

let rec replace
    (i:Id.t)
    (e_with:Expr.t)
    (e:Expr.t)
  : Expr.t =
  let replace_simple = replace i e_with in
  begin match e with
    | Var i' ->
      if is_equal (compare i i') then
        e_with
      else
        e
    | App (e1,e2) ->
      App (replace_simple e1, replace_simple e2)
    | Func ((i',t),e') ->
      if is_equal (compare i i') then
        e
      else
        Func ((i',t),replace_simple e')
    | Ctor (i,e) ->
      Ctor (i, replace_simple e)
    | Match (e,i',branches) ->
      let branches =
        if is_equal @$ Id.compare i i' then
          branches
        else
          List.map
            ~f:(fun (i,e) -> (i,replace_simple e))
            branches
      in
      Match (replace_simple e, i', branches)
    | Fix (i',t,e') ->
      if is_equal @$ Id.compare i i' then
        e
      else
        Fix (i,t,replace_simple e')
    | Tuple es ->
      Tuple
        (List.map ~f:replace_simple es)
    | Proj (i,e) ->
      Proj (i,replace_simple e)
  end


let rec evaluate
    (e:Expr.t)
  : Value.t =
  begin match e with
    | Var _ -> failwith "unbound variable"
    | App (e1,e2) ->
      let ((i,_),e1) = Expr.destruct_func_exn e1 in
      evaluate @$ replace i e2 (Value.to_exp @$ evaluate e1)
    | Func (a,e) -> Value.func a e
    | Ctor (i,e) -> Value.ctor i (evaluate e)
    | Match (e,i,branches) ->
      let (choice,v) = Value.destruct_ctor_exn (evaluate e) in
      let branch =
        List.Assoc.find_exn
          ~equal:(is_equal %% Id.compare)
          branches
          choice
      in
      evaluate @$ replace i (Value.to_exp v) branch
    | Fix (i,_,e') ->
      evaluate @$ replace i e e'
    | Tuple es ->
      Value.tuple (List.map ~f:evaluate es)
    | Proj (i,e) ->
      let vs = Value.destruct_tuple_exn @$ evaluate e in
      List.nth_exn vs i
  end
