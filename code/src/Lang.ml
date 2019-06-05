open Core

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
  type t = Param.t list * Expr.t
  [@@deriving bin_io, eq, hash, ord, sexp, show]
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
    let t' = Type.mk_var (Id.mk_prime "t")
     in match ito with
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
