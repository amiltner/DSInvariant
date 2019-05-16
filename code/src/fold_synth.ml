(*open MyStdlib
open Lang

let rec element_of_type_of_size
    ~(tc:TypeContext.t)
    ~(ec:ExprContext.t)
    ~(problem:problem)
    ~(size:int)
    (t:Type.t)
  : Expr.t option =
  begin match t with
    | Var i ->
      element_of_type_of_size
        ~tc
        ~ec
        ~problem
        ~size
        (TypeContext.lookup_exn problem.tc i)
    | Arr _ ->
      None
    | Tuple ts -> 
    | _ -> failwith "ah"
  end

let element_of_type
    ~(problem:problem)
    (t:Type.t)
  : Expr.t =
  fold_until_completion
    ~f:(fun i ->
        begin match element_of_type_of_size ~problem ~size:i t with
          | None -> Left (i+1)
          | Some e -> Right e
        end)
    0

let rec replace_var_with_type
    (t:Type.t)
    (tid:Id.t)
    (desired:Type.t)
  : Type.t =
  let replace_var_with_type = fun t -> replace_var_with_type t tid desired in
  begin match t with
    | Var i ->
      if is_equal @$ Id.compare i tid then
        desired
      else
        t
    | Arr _ ->
      t
    | Tuple ts ->
      Type.mk_tuple @$ List.map ~f:replace_var_with_type ts
    | Mu _ ->
      t
    | Variant branches ->
      Type.mk_variant @$
      List.map ~f:(fun (i,t) -> (i,replace_var_with_type t)) branches
  end

let synth_fold
    ~(problem:problem)
    ~(folded_type:Type.t)
    ~(desired_end_type:Type.t)
  : Expr.t =
  let (tid,t_inner) = Type.destruct_mu_exn folded_type in
  let desired_type = replace_var_with_type t_inner tid desired_end_type in
  element_of_type ~problem desired_type
*)
