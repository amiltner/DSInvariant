open MyStdlib
open Lang

module IdSet = SetOf(Id)
module MythLang = Myth.Lang
module TypeToType = DictOf(Type)(MythLang.Type)

let merge_tis tt1 tt2 =
  TypeToType.from_kvp_list @$
  TypeToType.merge
    ~combiner:(fun v1 v2 ->
        if is_equal @$ MythLang.Type.compare v1 v2 then
          v1
        else
          failwith "conflict")
    ~only_d1_fn:ident
    ~only_d2_fn:ident
    tt1
    tt2

let bigmerge_tis
    (rvs:TypeToType.t list)
  : TypeToType.t =
  fold_on_head_with_default
    ~f:merge_tis
    ~default:TypeToType.empty
    rvs

let rec to_myth_type
    (real_vars:IdSet.t)
    (adjoining_var:Id.t option)
    (tt:TypeToType.t)
    (t:Type.t)
  : (MythLang.id * MythLang.ctor list) list * MythLang.typ * TypeToType.t =
  let to_myth_type_simple = to_myth_type real_vars adjoining_var tt in
  begin match TypeToType.lookup tt t with
    | Some mt -> ([],mt,tt)
    | None ->
      begin match t with
        | Var v ->
          if IdSet.member real_vars v then
            ([],MythLang.TBase v,tt)
          else
            failwith ("non-real var: " ^ v)
        | Arr (t1,t2) ->
          let (ds1,mt1,tt1) = to_myth_type_simple t1 in
          let (ds2,mt2,tt2) = to_myth_type_simple t2 in
          ((ds1@ds2), MythLang.TArr (mt1, mt2), merge_tis tt1 tt2)
        | Tuple ts ->
          if List.length ts = 0 then
            ([],MythLang.TUnit,tt)
          else
            let (ds,mts,tts) = List.unzip3 @$ List.map ~f:to_myth_type_simple ts in
            let tt = bigmerge_tis tts in
            (List.concat ds, MythLang.TTuple mts, tt)
        | Mu (i,t) ->
          (*let fresh = IdSet.fresh_id used_ids i in*)
          assert
            (Option.is_some @$ Type.destruct_variant t
              &&
              (is_equal @$
              (option_compare Id.compare)
                (Some i)
                adjoining_var));
          let real_vars = IdSet.insert i real_vars in
          to_myth_type real_vars adjoining_var tt t
        | Variant branches ->
          let i = Option.value_exn adjoining_var in
          let (unflattened_bs,its,tts) =
            List.unzip3 @$
            List.map
              ~f:(fun (i,t) ->
                  let (b,mt,tt) = to_myth_type real_vars adjoining_var tt t in
                  (b,(i,mt),tt))
              branches
          in
          let tt = merge_tis tt (bigmerge_tis tts) in
          let bs = List.concat unflattened_bs in
          let tt = TypeToType.insert tt (Variant branches) (MythLang.TBase i) in
          ((i,its)::bs, MythLang.TBase i,tt)
      end
  end

let to_myth_type_basic
    (tt:TypeToType.t)
    (t:Type.t)
  : MythLang.typ =
  snd3 @$ to_myth_type IdSet.empty None tt t

let rec to_myth_exp
    (tt:TypeToType.t)
    (e:Expr.t)
  : MythLang.exp =
  let to_myth_exp = to_myth_exp tt in
  begin match e with
    | Var i -> MythLang.EVar i
    | App (e1,e2) -> MythLang.EApp (to_myth_exp e1, to_myth_exp e2)
    | Func ((i,t),e) ->
      let mt = to_myth_type_basic tt t in
      MythLang.EFun ((i,mt), to_myth_exp e)
    | Ctor (i,e) ->
      ECtor (i,to_myth_exp e)
    | Match (e,i,branches) ->
      let me = to_myth_exp e in
      let mbranches =
        List.map
          ~f:(fun (b,e) -> ((b,Some (MythLang.PVar i)), to_myth_exp e))
          branches
      in
      MythLang.EMatch (me,mbranches)
    | Fix (i,t,e) ->
      let (t1,t2) = Type.destruct_arr_exn t in
      let ((i',t'),e) = Expr.destruct_func_exn e in
      assert (is_equal @$ Type.compare t1 t');
      let mt1 = to_myth_type_basic tt t1 in
      let mt2 = to_myth_type_basic tt t2 in
      let me = to_myth_exp e in
      MythLang.EFix (i, (i',mt1), mt2, me)
    | Tuple es ->
      if List.length es = 0 then
        MythLang.EUnit
      else
        MythLang.ETuple (List.map ~f:to_myth_exp es)
    | Proj (i,e) ->
      MythLang.EProj (i+1, to_myth_exp e)
  end

let convert_decl_list_to_myth
    (ec:ExprContext.t)
    (ds:Declaration.t list)
  : MythLang.decl list * TypeToType.t =
  let (tt,ds) =
    List.fold_left
      ~f:(fun (tt,dsrev) d ->
          Declaration.fold
            ~type_f:(fun i t ->
                let (ctors,mt,tt) = to_myth_type IdSet.empty (Some i) tt t in
                let new_ds =
                  List.map
                    ~f:(fun (i,cs) -> MythLang.DData (i,cs))
                    ctors
                in
                let tt = TypeToType.insert tt (Type.mk_var i) mt in
                (tt,new_ds@dsrev))
            ~expr_f:(fun i e ->
                let new_d =
                  MythLang.DLet
                    (i
                    ,false
                    ,[]
                    ,to_myth_type_basic tt (ExprContext.lookup_exn ec i)
                    ,to_myth_exp tt e)
                in
                (tt,new_d::dsrev))
            d)
      ~init:(TypeToType.empty,[])
      ds
  in
  (List.rev ds, tt)

let convert_problem_examples_type_to_myth
    (p:problem)
    (examples:(Expr.t * Expr.t) list)
  : MythLang.decl list * (MythLang.exp * MythLang.exp) list * MythLang.typ =
  let (decls,modi,_,_) = p.unprocessed in
  let (ds,tt) = convert_decl_list_to_myth p.ec (decls@modi) in
  let examples =
    List.map
      ~f:(fun (e1,e2) -> (to_myth_exp tt e1, to_myth_exp tt e2))
      examples
  in
  let t = to_myth_type_basic tt (Type.mk_var "t") in
  (ds,examples,t)
