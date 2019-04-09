open MyStdlib

module Id =
struct
  type t = string
  [@@deriving ord, show, hash]
end

module Type =
struct
  type t =
    | Var of Id.t
    | Arr  of t * t
    | Tuple of t list
    | Mu of Id.t * t
    | Variant of (Id.t * t) list
  [@@deriving ord, show, hash]

  let mk_var
      (i:Id.t)
    : t =
    Var i

  let mk_arr
      (t1:t)
      (t2:t)
    : t =
    Arr (t1,t2)

  let mk_tuple
      (ts:t list)
    : t =
    Tuple ts

  let mk_mu
      (i:Id.t)
      (t:t)
    : t =
    if (is_equal @$ compare t (mk_var i)) then
      failwith "cannot do infinite loop";
    Mu (i,t)

  let mk_variant
      (branches:(Id.t * t) list)
    : t =
    Variant branches

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

  let variant
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

  let tuple
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
end

module Arg =
struct
  type t = Id.t * Type.t
  [@@deriving ord, show, hash]
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
  [@@deriving ord, show, hash]

  let var
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

  let app
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
      | App (e1,e2) -> Option.some @$ f e1 e2
      | _ -> None
    end

  let destruct_app
    : t -> (t * t) option =
    apply_app ~f:(fun e1 e2 -> (e1,e2))

  let destruct_app_exn
    (e:t)
    : t * t =
    Option.value_exn (destruct_app e)

  let func
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
      | Func (a,e2) -> Option.some @$ f a e2
      | _ -> None
    end

  let destruct_func
    : t -> (Arg.t * t) option =
    apply_func ~f:(fun a e2 -> (a,e2))

  let destruct_func_exn
      (e:t)
    : Arg.t * t =
    Option.value_exn (destruct_func e)

  let ctor
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
      | Ctor (i,e2) -> Option.some @$ f i e2
      | _ -> None
    end

  let destruct_ctor
    : t -> (Id.t * t) option =
    apply_ctor ~f:(fun a e2 -> (a,e2))

  let destruct_ctor_exn
      (e:t)
    : Id.t * t =
    Option.value_exn (destruct_ctor e)

  let tuple
      (es:t list)
    : t =
    Tuple es

  let apply_tuple
      (type a)
      ~(f:t list -> a)
      (e:t)
    : a option =
    begin match e with
      | Tuple es -> Option.some @$ f es
      | _ -> None
    end

  let destruct_tuple
    : t -> t list option =
    apply_tuple ~f:ident

  let destruct_tuple_exn
      (e:t)
    : t list =
    Option.value_exn (destruct_tuple e)

  let proj
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
      | Proj (i,e2) -> Option.some @$ f i e2
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
      | Match (e,i,branches) -> Option.some @$ f e i branches
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
      | Fix (i,t,e) -> Option.some @$ f i t e
      | _ -> None
    end

  let destruct_fix
    : t -> (Id.t * Type.t * t) option =
    apply_fix ~f:(fun i t e -> (i,t,e))

  let destruct_fix_exn
      (e:t)
    : Id.t * Type.t * t =
    Option.value_exn (destruct_fix e)

  let unit : t = tuple []
end

module Context(D : Data) =
struct
  include DictOf(Id)(D)
end

module ExprContext = Context(Type)
module TypeContext = Context(Type)
module VariantContext = Context(ListOf(PairOf(Id)(Type)))

module ModuleSpec =
struct
  type t = Id.t * (Id.t * Type.t) list
  [@@deriving ord, show, hash]
end

module Declaration =
struct
  type t =
    | TypeDeclaration of Id.t * Type.t
    | ExprDeclaration of Id.t * Expr.t
  [@@deriving ord, show, hash]

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
  [@@deriving ord, show, hash]
end

module UniversalFormula =
struct
  type t = Arg.t list * Expr.t
end

module Value =
struct
  type t =
    | Func of Arg.t * Expr.t
    | Ctor of Id.t * t
    | Tuple of t list

  let func
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
      | Func (a,e2) -> Option.some @$ f a e2
      | _ -> None
    end

  let destruct_func
    : t -> (Arg.t * Expr.t) option =
    apply_func ~f:(fun a e2 -> (a,e2))

  let destruct_func_exn
      (v:t)
    : Arg.t * Expr.t =
    Option.value_exn (destruct_func v)

  let ctor
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
      | Ctor (i,v) -> Option.some @$ f i v
      | _ -> None
    end

  let destruct_ctor
    : t -> (Id.t * t) option =
    apply_ctor ~f:(fun i v -> (i,v))

  let destruct_ctor_exn
      (v:t)
    : Id.t * t =
    Option.value_exn (destruct_ctor v)

  let tuple
      (vs:t list)
    : t =
    Tuple vs

  let apply_tuple
      (type a)
      ~(f:t list -> a)
      (v:t)
    : a option =
    begin match v with
      | Tuple vs -> Option.some @$ f vs
      | _ -> None
    end

  let destruct_tuple
    : t -> t list option =
    apply_tuple ~f:ident

  let destruct_tuple_exn
      (v:t)
    : t list =
    Option.value_exn (destruct_tuple v)

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
      ~func_f:Expr.func
      ~ctor_f:Expr.ctor
      ~tuple_f:Expr.tuple
end

type problem = Declaration.t list * ModuleImplementation.t * ModuleSpec.t * UniversalFormula.t