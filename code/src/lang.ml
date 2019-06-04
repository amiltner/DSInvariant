open Core

module Id =
struct
  type t = string
  [@@deriving bin_io, eq, hash, ord, sexp, show]

  let mk_prime (x:t) : t = x ^ "'"
end

module Type =
struct
  type t =
    | Var of Id.t
    | Arr  of t * t
    | Tuple of t list
    | Mu of Id.t * t
    | Variant of (Id.t * t) list
  [@@deriving bin_io, eq, hash, ord, sexp, show]

  let mk_var
      (i:Id.t)
    : t =
    Var i

  let mk_arr
      (t1:t)
      (t2:t)
    : t =
    Arr (t1,t2)

  let mk_mu
      (i:Id.t)
      (t:t)
    : t =
    if equal t (mk_var i) then
      failwith "cannot do infinite loop";
    Mu (i,t)

  let fold
      (type a)
      ~(base_f:Id.t -> a)
      ~(arr_f:a -> a -> a)
      ~(tuple_f:a list -> a)
      ~(mu_f:Id.t -> a -> a)
      ~(variant_f:(Id.t * a) list -> a)
      (e:t)
    : a =
    let rec fold_internal
        (e:t)
      : a =
      begin match e with
        | Var v -> base_f v
        | Arr (e1,e2) -> arr_f (fold_internal e1) (fold_internal e2)
        | Tuple es -> tuple_f (List.map ~f:fold_internal es)
        | Mu (i,e) -> mu_f i (fold_internal e)
        | Variant variants ->
          variant_f (List.map ~f:(fun (i,t) -> (i,fold_internal t)) variants)
      end
    in
    fold_internal e

  let arr_apply
      (type a)
      ~(f:t -> t -> a)
      (ty:t)
    : a option =
    begin match ty with
      | Arr (ty1,ty2) -> Some (f ty1 ty2)
      | _ -> None
    end

  let destruct_arr
    : t -> (t * t) option =
    arr_apply ~f:(fun ty1 ty2 -> (ty1,ty2))

  let destruct_arr_exn
      (t:t)
    : t * t =
    Option.value_exn (destruct_arr t)

  let id_apply
      (type a)
      ~(f:Id.t -> a)
      (ty:t)
    : a option =
    begin match ty with
      | Var v -> Some (f v)
      | _ -> None
    end

  let destruct_id
    : t -> Id.t option =
    id_apply ~f:ident

  let destruct_id_exn
    (x:t)
    : Id.t =
    Option.value_exn
      (destruct_id x)

  let mk_variant
      (vs:(Id.t * t) list)
    : t =
    Variant vs

  let variant_apply
      (type a)
      ~(f:(Id.t * t) list -> a)
      (ty:t)
    : a option =
    begin match ty with
      | Variant its -> Some (f its)
      | _ -> None
    end

  let destruct_variant
    : t -> (Id.t * t) list option =
    variant_apply ~f:ident

  let destruct_variant_exn
    (t:t)
    : (Id.t * t) list =
    Option.value_exn (destruct_variant t)

  let mk_tuple
    (ts:t list)
    : t =
    Tuple ts

  let tuple_apply
      (type a)
      ~(f:t list -> a)
      (ty:t)
    : a option =
    begin match ty with
      | Tuple ts -> Some (f ts)
      | _ -> None
    end

  let destruct_tuple
    : t -> (t list) option =
    tuple_apply ~f:ident

  let destruct_tuple_exn
      (t:t)
    : t list =
    Option.value_exn (destruct_tuple t)

  let mu_apply
      (type a)
      ~(f:Id.t -> t -> a)
      (ty:t)
    : a option =
    begin match ty with
      | Mu (i,t)-> Some (f i t)
      | _ -> None
    end

  let destruct_mu
    : t -> (Id.t * t) option =
    mu_apply ~f:(fun i t -> (i,t))

  let destruct_mu_exn
      (t:t)
    : Id.t * t =
    Option.value_exn (destruct_mu t)

  let mk_unit : t = mk_tuple []

  let mk_t_var : t = mk_var "t"

  let mk_bool_var : t = mk_var "bool"

  let size
    : t -> int =
    fold
      ~base_f:(fun _ -> 1)
      ~arr_f:(fun x y -> x+y+1)
      ~tuple_f:(fun ss -> List.fold_left~f:(+) ~init:1 ss)
      ~mu_f:(fun _ s -> s+1)
      ~variant_f:(fun bs ->
          List.fold
            ~f:(fun acc (_,i) -> i+acc)
            ~init:1
            bs)
end

module Arg =
struct
  type t = Id.t * Type.t
  [@@deriving bin_io, eq, hash, ord, sexp, show]
end

module Expr =
struct
  type t =
    | Var of Id.t
    | App of t * t
    | Func of Arg.t * t
    | Ctor of Id.t * t
    | Match of t * Id.t * (Id.t * t) list
    | Fix  of Id.t * Type.t * t
    | Tuple of t list
    | Proj of int * t
  [@@deriving bin_io, eq, hash, ord, sexp, show]

  let mk_var
      (i:Id.t)
    : t =
    Var i

  let fold
      (type a)
      ~(var_f:Id.t -> a)
      ~(app_f:a -> a -> a)
      ~(func_f:Arg.t -> a -> a)
      ~(ctor_f:Id.t -> a -> a)
      ~(match_f:a -> Id.t -> (Id.t * a) list -> a)
      ~(fix_f:Id.t -> Type.t -> a -> a)
      ~(tuple_f:a list -> a)
      ~(proj_f:int -> a -> a)
      (e:t)
    : a =
    let rec fold_internal
        (e:t)
      : a =
      begin match e with
        | Var v -> var_f v
        | App (e1,e2) -> app_f (fold_internal e1) (fold_internal e2)
        | Func (a,e) -> func_f a (fold_internal e)
        | Ctor (v,e) -> ctor_f v (fold_internal e)
        | Match (e,i,branches) ->
          match_f
            (fold_internal e)
            i
            (List.map ~f:(fun (i,e') -> (i,fold_internal e')) branches)
        | Fix (i,t,e) ->
          fix_f
            i
            t
            (fold_internal e)
        | Tuple es ->
          tuple_f
            (List.map ~f:fold_internal es)
        | Proj (i,e) ->
          proj_f
            i
            (fold_internal e)
      end
    in
    fold_internal e

  let mk_app
      (e1:t)
      (e2:t)
    : t =
    App (e1,e2)

  let apply_app
      (type a)
      ~(f:t -> t -> a)
      (e:t)
    : a option =
    begin match e with
      | App (e1,e2) -> Some (f e1 e2)
      | _ -> None
    end

  let destruct_app
    : t -> (t * t) option =
    apply_app ~f:(fun e1 e2 -> (e1,e2))

  let destruct_app_exn
    (e:t)
    : t * t =
    Option.value_exn (destruct_app e)

  let mk_func
      (a:Arg.t)
      (e:t)
    : t =
    Func (a,e)

  let apply_func
      (type a)
      ~(f:Arg.t -> t -> a)
      (e:t)
    : a option =
    begin match e with
      | Func (a,e2) -> Some (f a e2)
      | _ -> None
    end

  let destruct_func
    : t -> (Arg.t * t) option =
    apply_func ~f:(fun a e2 -> (a,e2))

  let destruct_func_exn
      (e:t)
    : Arg.t * t =
    Option.value_exn (destruct_func e)

  let mk_ctor
      (i:Id.t)
      (e:t)
    : t =
    Ctor (i,e)

  let apply_ctor
      (type a)
      ~(f:Id.t -> t -> a)
      (e:t)
    : a option =
    begin match e with
      | Ctor (i,e2) -> Some (f i e2)
      | _ -> None
    end

  let destruct_ctor
    : t -> (Id.t * t) option =
    apply_ctor ~f:(fun a e2 -> (a,e2))

  let destruct_ctor_exn
      (e:t)
    : Id.t * t =
    Option.value_exn (destruct_ctor e)

  let mk_tuple
      (es:t list)
    : t =
    Tuple es

  let apply_tuple
      (type a)
      ~(f:t list -> a)
      (e:t)
    : a option =
    begin match e with
      | Tuple es -> Some (f es)
      | _ -> None
    end

  let destruct_tuple
    : t -> t list option =
    apply_tuple ~f:ident

  let destruct_tuple_exn
      (e:t)
    : t list =
    Option.value_exn (destruct_tuple e)

  let mk_proj
      (i:int)
      (e:t)
    : t =
    Proj (i,e)

  let apply_proj
      (type a)
      ~(f:int -> t -> a)
      (e:t)
    : a option =
    begin match e with
      | Proj (i,e2) -> Some (f i e2)
      | _ -> None
    end

  let destruct_proj
    : t -> (int * t) option =
    apply_proj ~f:(fun a e2 -> (a,e2))

  let destruct_proj_exn
      (e:t)
    : int * t =
    Option.value_exn (destruct_proj e)

  let mk_match
      (e:t)
      (binder:Id.t)
      (branches:(Id.t * t) list)
    : t =
    Match (e,binder,branches)

  let apply_match
      (type a)
      ~(f:t -> Id.t -> (Id.t * t) list -> a)
      (e:t)
    : a option =
    begin match e with
      | Match (e,i,branches) -> Some (f e i branches)
      | _ -> None
    end

  let destruct_match
    : t -> (t * Id.t * (Id.t * t) list) option =
    apply_match ~f:(fun e i branches -> (e,i,branches))

  let destruct_match_exn
      (e:t)
    : t * Id.t * (Id.t * t) list =
    Option.value_exn (destruct_match e)

  let mk_fix
      (i:Id.t)
      (t:Type.t)
      (e:t)
    : t =
    Fix (i,t,e)

  let apply_fix
      (type a)
      ~(f:Id.t -> Type.t -> t -> a)
      (e:t)
    : a option =
    begin match e with
      | Fix (i,t,e) -> Some (f i t e)
      | _ -> None
    end

  let destruct_fix
    : t -> (Id.t * Type.t * t) option =
    apply_fix ~f:(fun i t e -> (i,t,e))

  let destruct_fix_exn
      (e:t)
    : Id.t * Type.t * t =
    Option.value_exn (destruct_fix e)

  let rec replace
      (i:Id.t)
      (e_with:t)
      (e:t)
    : t =
    let replace_simple = replace i e_with in
    begin match e with
      | Var i' ->
        if String.equal i i' then
          e_with
        else
          e
      | App (e1,e2) ->
        App (replace_simple e1, replace_simple e2)
      | Func ((i',t),e') ->
        if String.equal i i' then
          e
        else
          Func ((i',t),replace_simple e')
      | Ctor (i,e) ->
        Ctor (i, replace_simple e)
      | Match (e,i',branches) ->
        let branches =
          if Id.equal i i' then
            branches
          else
            List.map
              ~f:(fun (i,e) -> (i,replace_simple e))
              branches
        in
        Match (replace_simple e, i', branches)
      | Fix (i',t,e') ->
        if Id.equal i i' then
          e
        else
          Fix (i',t,replace_simple e')
      | Tuple es ->
        Tuple
          (List.map ~f:replace_simple es)
      | Proj (i,e) ->
        Proj (i,replace_simple e)
    end

  let replace_holes
      ~(i_e:(Id.t * t) list)
      (e:t)
    : t =
    List.fold_left
      ~f:(fun acc (i,e) -> replace i e acc)
      ~init:e
      i_e

  let mk_unit : t = mk_tuple []

  let mk_true_exp
    : t =
    mk_ctor "True" (mk_tuple [])

  let mk_false_exp
    : t =
    mk_ctor "False" (mk_tuple [])

  let mk_constant_func
      (t:Type.t)
      (e:t)
    : t =
    mk_func ("x",t) e

  let mk_constant_true_func
      (t:Type.t)
    : t =
    mk_constant_func t mk_true_exp

  let mk_constant_false_func
      (t:Type.t)
    : t =
    mk_constant_func t mk_false_exp

  let mk_identity_func
      (t:Type.t)
    : t =
    mk_func ("x",t) (mk_var "x")

  let mk_and_func : t = mk_var "and"

  let rec contains_var
      (v:Id.t)
      (e:t)
    : bool =
    let contains_var_simple = contains_var v in
    begin match e with
      | Var i -> Id.equal i v
      | App (e1,e2) -> contains_var_simple e1 || contains_var_simple e2
      | Func ((i,_),e) ->
        if Id.equal i v then
          false
        else
          contains_var_simple e
      | Ctor (_,e) -> contains_var_simple e
      | Match (e,i,branches) ->
        contains_var_simple e ||
        (if Id.equal i v then
           false
         else
           List.exists
             ~f:(fun (_,e) -> contains_var_simple e)
             branches)
      | Fix (i,_,e) ->
        if Id.equal i v then
          false
        else
          contains_var_simple e
      | Tuple es -> List.exists ~f:contains_var_simple es
      | Proj (_,e) -> contains_var_simple e
    end

  let rec simplify
      (e:t)
    : t =
    begin match e with
      | Var _ -> e
      | App (e1,e2) ->
        mk_app (simplify e1) (simplify e2)
      | Func (a,e) ->
        mk_func a (simplify e)
      | Match (e,v,branches) ->
        mk_match
          (simplify e)
          v
          (List.map ~f:(fun (i,e) -> (i,simplify e)) branches)
      | Fix (i,t,e) ->
        let e = simplify e in
        if not (contains_var i e) then
          e
        else
          mk_fix i t e
      | Ctor (i,e) ->
        mk_ctor i (simplify e)
      | Tuple es -> mk_tuple (List.map ~f:simplify es)
      | Proj (i,e) -> mk_proj i (simplify e)
    end

  let and_exps
      (e1:t)
      (e2:t)
    : t =
    mk_app (mk_app mk_and_func e1) e2

  let is_func
      ~(func_internals:t)
      (e:t)
    : bool =
    begin match e with
      | Func (_,e) -> equal e func_internals
      | _ -> false
    end

  let and_predicates (e1:t) (e2:t) : t =
    let is_true_func = is_func ~func_internals:mk_true_exp in
    let is_false_func = is_func ~func_internals:mk_false_exp in
    if is_true_func e1 then
      e2
    else if is_true_func e2 then
      e1
    else if is_false_func e1 || is_false_func e2 then
      mk_constant_false_func (Type.mk_var "t")
    else
      let var = "x" in
      let var_exp = mk_var var in
      let apped_e1 = mk_app e1 var_exp in
      let apped_e2 = mk_app e2 var_exp in
      mk_func
        (var,Type.mk_var "t")
        (and_exps apped_e1 apped_e2)

  let mk_let_in (i:Id.t) (t:Type.t) (e1:t) (e2:t) : t =
    mk_app (mk_func (i,t) e2) e1

  let size : t -> int =
    fold ~var_f:(fun _ -> 1)
         ~app_f:(fun x y -> x+y+1)
         ~func_f:(fun (_,t) i -> 1 + (Type.size t) + i)
         ~ctor_f:(fun _ s -> s+1)
         ~match_f:(fun s _ bs -> List.fold_left bs ~init:(s+1)
                                                ~f:(fun acc (_,s) -> s+acc))
         ~fix_f:(fun _ t s -> 1 + (Type.size t) + s)
         ~tuple_f:(List.fold_left~f:(+) ~init:1)
         ~proj_f:(fun _ i -> i+2)
end

module Context = struct
  include Map.Make(Id)
  include Provide_bin_io(Id)
  include Provide_hash(Id)
end

module ExprContext = struct
  type key = Context.Key.t
  type value = Type.t

  type t = Type.t Context.t
  [@@deriving bin_io, eq, hash, ord, sexp]
end

module TypeContext = struct
  type key = Context.Key.t
  type value = Type.t

  type t = Type.t Context.t
  [@@deriving bin_io, eq, hash, ord, sexp]
end

module VariantContext = struct
  type key = Context.Key.t
  type value = (Id.t * Type.t) list

  type t = (Id.t * Type.t) list Context.t
  [@@deriving bin_io, eq, hash, ord, sexp]
end

module ModuleSpec =
struct
  type t = Id.t * (Id.t * Type.t) list
  [@@deriving bin_io, eq, hash, ord, sexp, show]
end

module Declaration =
struct
  type t =
    | TypeDeclaration of Id.t * Type.t
    | ExprDeclaration of Id.t * Expr.t
  [@@deriving bin_io, eq, hash, ord, sexp, show]

  let fold
      (type a)
      ~(type_f:Id.t -> Type.t -> a)
      ~(expr_f:Id.t -> Expr.t -> a)
      (d:t) =
    begin match d with
      | TypeDeclaration (i,t) -> type_f i t
      | ExprDeclaration (i,e) -> expr_f i e
    end

  let type_dec
      (i:Id.t)
      (t:Type.t)
    : t =
    TypeDeclaration (i,t)

  let expr_dec
      (i:Id.t)
      (e:Expr.t)
    : t =
    ExprDeclaration (i,e)
end

module ModuleImplementation =
struct
  type t = Declaration.t list
  [@@deriving bin_io, eq, hash, ord, sexp, show]
end

module UniversalFormula =
struct
  type t = Arg.t list * Expr.t
  [@@deriving bin_io, eq, hash, ord, sexp, show]
end

module Value =
struct
  type t =
    | Func of Arg.t * Expr.t
    | Ctor of Id.t * t
    | Tuple of t list
  [@@deriving bin_io, eq, hash, ord, sexp, show]

  let mk_func
      (a:Arg.t)
      (e:Expr.t)
    : t =
    Func (a,e)

  let apply_func
      (type a)
      ~(f:Arg.t -> Expr.t -> a)
      (v:t)
    : a option =
    begin match v with
      | Func (a,e2) -> Some (f a e2)
      | _ -> None
    end

  let destruct_func
    : t -> (Arg.t * Expr.t) option =
    apply_func ~f:(fun a e2 -> (a,e2))

  let destruct_func_exn
      (v:t)
    : Arg.t * Expr.t =
    Option.value_exn (destruct_func v)

  let mk_ctor
      (i:Id.t)
      (v:t)
    : t =
    Ctor (i,v)

  let apply_ctor
      (type a)
      ~(f:Id.t -> t -> a)
      (v:t)
    : a option =
    begin match v with
      | Ctor (i,v) -> Some (f i v)
      | _ -> None
    end

  let destruct_ctor
    : t -> (Id.t * t) option =
    apply_ctor ~f:(fun i v -> (i,v))

  let destruct_ctor_exn
      (v:t)
    : Id.t * t =
    Option.value_exn (destruct_ctor v)

  let mk_tuple
      (vs:t list)
    : t =
    Tuple vs

  let apply_tuple
      (type a)
      ~(f:t list -> a)
      (v:t)
    : a option =
    begin match v with
      | Tuple vs -> Some (f vs)
      | _ -> None
    end

  let destruct_tuple
    : t -> t list option =
    apply_tuple ~f:ident

  let destruct_tuple_exn
      (v:t)
    : t list =
    Option.value_exn (destruct_tuple v)

  let mk_true : t = mk_ctor "True" (mk_tuple [])

  let mk_false : t = mk_ctor "False" (mk_tuple [])

  let rec fold
      ~(func_f:Arg.t -> Expr.t -> 'a)
      ~(ctor_f:Id.t -> 'a -> 'a)
      ~(tuple_f:'a list -> 'a)
      (v:t)
    : 'a =
    let fold_simple = fold ~func_f ~ctor_f ~tuple_f in
    begin match v with
      | Func (a,e) -> func_f a e
      | Ctor (i,v) -> ctor_f i (fold_simple v)
      | Tuple vs -> tuple_f (List.map ~f:fold_simple vs)
    end

  let to_exp
    : t -> Expr.t =
    fold
      ~func_f:Expr.mk_func
      ~ctor_f:Expr.mk_ctor
      ~tuple_f:Expr.mk_tuple

  let rec from_exp
    (e:Expr.t)
    : t option =
    begin match e with
      | Func (a,e)
        -> Some (mk_func a e)
      | Ctor (i,e)
        -> Option.map ~f:(mk_ctor i) (from_exp e)
      | Tuple es
        -> Option.map ~f:mk_tuple (Some (List.filter_map es ~f:from_exp))
      | Var _
      | App _
      | Proj _
      | Match _
      | Fix _ -> None
    end

  let from_exp_exn (e:Expr.t) : t =
    Option.value_exn (from_exp e)

  let rec subvalues (v:t) : t list =
    v :: begin match v with
           | Func _ -> []
           | Ctor (_,v) -> subvalues v
           | Tuple vs -> List.concat_map ~f:subvalues vs
         end

  let strict_subvalues (e:t) : t list =
    List.tl_exn (subvalues e)
end

type unprocessed_problem =
  Declaration.t list * ModuleImplementation.t * ModuleSpec.t * UniversalFormula.t * Type.t option
[@@deriving bin_io, eq, hash, ord, sexp]

type problem =
  {
    module_type  : Type.t                 ;
    ec           : ExprContext.t          ;
    tc           : TypeContext.t          ;
    vc           : VariantContext.t       ;
    mod_vals     : (Expr.t * Type.t) list ;
    post         : UniversalFormula.t     ;
    eval_context : (Id.t * Expr.t) list   ;
    unprocessed  : unprocessed_problem    ;
    accumulator  : Type.t option          ;
  }
[@@deriving bin_io, eq, hash, make, ord, sexp]

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
        if Id.equal i i' then
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
  let t = Context.find_exn tc "t" in
  let tv = Type.destruct_id_exn t in
  let t = Context.find_exn tc tv in
  let ito = Type.destruct_mu t in
  begin match ito with
    | None -> t
    | Some (i,t) ->
      type_to_folded_type_internal i t
  end

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
          if Id.equal i i' then
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
    let t = Context.find_exn tc "t" in
    let tv = Type.destruct_id_exn t in
    let t = Context.find_exn tc tv in
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
