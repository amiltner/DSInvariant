open Core

module T = struct
  include Map.Make(Id)
  include Provide_bin_io(Id)
  include Provide_hash(Id)
end

include T

module Exprs = struct
  type key = T.Key.t
  type value = Type.t

  type t = Type.t T.t
  [@@deriving bin_io, eq, hash, ord, sexp]
end

module Types = struct
  type key = T.Key.t
  type value = Type.t

  type t = Type.t T.t
  [@@deriving bin_io, eq, hash, ord, sexp]
end

module Variants = struct
  type key = T.Key.t
  type value = (Id.t * Type.t) list

  type t = (Id.t * Type.t) list T.t
  [@@deriving bin_io, eq, hash, ord, sexp]
end

let get_foldable_t (tc:Types.t) (fold_completion:Type.t) : Type.t =
  let rec type_to_folded_type_internal
      (i:Id.t)
      (t:Type.t)
    : Type.t =
    begin match t with
      | Named i' ->
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
      | Arrow _ | Mu _ -> t
    end
  in
  let t = find_exn tc "t" in
  let tv = Type.destruct_id_exn t in
  let t = find_exn tc tv in
  let ito = Type.destruct_mu t in
  begin match ito with
    | None -> t
    | Some (i,t) ->
      type_to_folded_type_internal i t
  end

let convert_foldable_to_full (tc : Types.t)
                             (fold_completion : Type.t)
                             : Expr.t =
    let convert_internal_id = "convert'" in
    let convert_internal_exp = Expr.mk_var convert_internal_id in
    let rec convert_foldable_internal
        (i:Id.t)
        (t:Type.t)
        (incoming_exp:Expr.t)
      : Expr.t =
      begin match t with
        | Named i' ->
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
        | Arrow _ ->
          incoming_exp
      end
    in
    let t = find_exn tc "t" in
    let tv = Type.destruct_id_exn t in
    let t = find_exn tc tv in
    let ito = Type.destruct_mu t in
    let t' = Type.mk_named (Id.mk_prime "t")
     in match ito with
        | None ->
          Expr.mk_func
            ("x",Type.mk_arrow t' t')
            (Expr.mk_var "x")
        | Some (i,t_internal) ->
          Expr.mk_func
            ("f",Type.mk_arrow
              t'
              fold_completion)
            (Expr.mk_fix
              convert_internal_id
              (Type.mk_arrow (Type._t) fold_completion)
              (Expr.mk_func
                  ("x" , Type._t)
                  (Expr.mk_app
                    (Expr.mk_var "f")
                    (convert_foldable_internal
                        i
                        t_internal
                        (Expr.mk_var "x")))))
