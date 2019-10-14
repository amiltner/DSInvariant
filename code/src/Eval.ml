open Core

let rec evaluate
    ~(tc:Context.Types.t)
    (e : Expr.t)
  : Value.t * Value.t list =
  match e with
  | Var i -> failwith ("unbound variable " ^ i)
  | App (e1,e2) ->
    let (v1,v1s) = evaluate ~tc e1 in
    let e1 = Value.to_exp v1 in
    let ((i,_),e1) = Expr.destruct_func_exn e1 in
    let (v2,v2s) = evaluate ~tc e2 in
    let e2 = Value.to_exp v2 in
    let (v,vs) = evaluate ~tc (Expr.replace i e2 e1) in
    (v,v1s@v2s@vs)
  | Func (a,e) ->
    (Value.mk_func a e,[])
  | Ctor (i,e) ->
    let (v,vs) = evaluate ~tc e in
    (Value.mk_ctor i v,vs)
  | Match (e,i,branches) as match_expr ->
    let (v,vs) = evaluate ~tc e in
    let (choice,v) = Value.destruct_ctor_exn v in
    let branch_o = List.Assoc.find ~equal:Id.equal branches choice in
    let branch =
      begin match branch_o with
        | None ->
          failwith
            ("constructor "
             ^ choice
             ^ " not matched: \n "
             ^ (Expr.show match_expr))
        | Some b -> b
      end
    in
    let (v,vs') = evaluate ~tc (Expr.replace i (Value.to_exp v) branch) in
    (v,vs@vs')
  | Fix (i,_,e') ->
    evaluate ~tc (Expr.replace i e e')
  | Tuple es ->
    let (vs,vsaccs) =
      List.unzip
        (List.map ~f:(evaluate ~tc) es)
    in
    (Value.mk_tuple vs,List.concat vsaccs)
  | Proj (i,e) ->
    let (v,vs) = evaluate ~tc e in
    (List.nth_exn (Value.destruct_tuple_exn v) i,vs)
  | Tagged (t,e) ->
    let (v,vs) = evaluate ~tc e in
    let rec propogate_tag
        (tc:Context.Types.t)
        (t:Type.t)
        (v:Value.t)
      : (Value.t * Value.t list) =
      let propogate_tag_simple = propogate_tag tc in
      if t = Type._t then
        (v,[v])
      else
        begin match t with
          | Named i ->
            propogate_tag_simple (Context.find_exn tc i) v
          | Arrow (_,t2) ->
            let (p,e) = Value.destruct_func_exn v in
            (Value.mk_func p (Expr.mk_tagged t2 e),[])
          | Tuple ts ->
            let vs = Value.destruct_tuple_exn v in
            let (vs,vaccs) =
              List.unzip
                (List.map2_exn ~f:propogate_tag_simple ts vs)
            in
            (Value.mk_tuple vs,List.concat vaccs)
          | Mu (i,t) ->
            let tc = Context.set tc ~key:i ~data:t in
            propogate_tag tc t v
          | Variant branches ->
            let (i,v) = Value.destruct_ctor_exn v in
            let t = List.Assoc.find_exn ~equal:Id.equal branches i in
            let (v,vs) = propogate_tag_simple t v in
            (Value.mk_ctor i v,vs)
        end
    in
    let (v,vs') = propogate_tag tc t v in
    (v,vs@vs')

let evaluate_with_holes
    ~(tc:Context.Types.t)
    ~eval_context:(i_e:(Id.t * Expr.t) list)
    (e:Expr.t)
  : Value.t * Value.t list =
  let e = Expr.replace_holes ~i_e e in
  evaluate ~tc e
