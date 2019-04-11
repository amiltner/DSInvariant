open Core
open Lang

let rec explode (binder: Expr.t) : Myth.Lang.pattern list -> (Expr.t * Id.t) list =
  let rec helper i acc = 
    function [@warning "-8"]
    | [] -> acc
    | (Myth.Lang.PVar id) :: plist
      -> helper (i + 1) (((Expr.Proj (i, binder)), id) :: acc) plist
    | (Myth.Lang.PTuple _plist) :: plist
      -> helper (i + 1) ((explode (Expr.Proj (i, binder)) _plist) @ acc) plist
   in helper 0 []

let rec convert_type : Myth.Lang.typ -> Type.t =
  function [@warning "-8"]
  | TBase id          -> Type.Var id
  | TArr (typ1, typ2) -> Type.Arr ((convert_type typ1), (convert_type typ2))
  | TTuple (typlist)  -> Type.Tuple (List.map ~f:convert_type typlist)
  | TUnit             -> Type.mk_unit

let convert_arg ((id, typ) : Myth.Lang.arg) : Arg.t =
  (id, convert_type typ)

let _FRESH_VAR_COUNTER = ref 0
let create_fresh_var () : Id.t =
  _FRESH_VAR_COUNTER := !_FRESH_VAR_COUNTER + 1 ;
  "N_fresh_var_" ^ Int.to_string (!_FRESH_VAR_COUNTER)

let rec convert_expr : Myth.Lang.exp -> Expr.t =
  function [@warning "-8"]
  | Myth.Lang.EUnit
    -> Expr.Tuple []
  | Myth.Lang.EVar id
    -> Expr.Var id
  | Myth.Lang.EApp (exp1, exp2)
    -> Expr.App ((convert_expr exp1), (convert_expr exp2))
  | Myth.Lang.ECtor (id, exp)
    -> Expr.Ctor (id, (convert_expr exp))
  | Myth.Lang.ETuple explist
    -> Expr.Tuple (List.map ~f:convert_expr explist)
  | Myth.Lang.EProj (int, exp)
    -> Expr.Proj (int, (convert_expr exp))
  | Myth.Lang.EFix (id, ((_, arg_typ) as arg), typ, body)
    -> Expr.Fix (id, (convert_type (Myth.Lang.TArr (arg_typ, typ))),
                 (Expr.Func ((convert_arg arg), (convert_expr body))))
  | Myth.Lang.EFun (arg, body)
    -> Expr.Func ((convert_arg arg), (convert_expr body))
  | Myth.Lang.ELet (id, _, arglist, typ, exp, body)
    -> let arglist = (List.map ~f:convert_arg arglist)
        in Expr.App ((Expr.Fix (id,
                                (List.fold
                                  arglist
                                  ~init:(convert_type typ)
                                  ~f:(fun etyp (_, t) -> Type.Arr (t, etyp))),
                                (List.fold
                                   arglist
                                   ~init:(convert_expr exp)
                                   ~f:(fun eacc arg -> Expr.Func (arg, eacc))))),
                     (convert_expr body))
  | Myth.Lang.EMatch (exp, branchlist)
    -> let fresh_var = create_fresh_var ()
        in Expr.Match ((convert_expr exp),
                       fresh_var,
                       (List.map ~f:(convert_branch fresh_var) branchlist))

and convert_branch (binder : Id.t) : Myth.Lang.branch -> (Id.t * Expr.t) =
  function [@warning "-8"]
  | ((id, Some (Myth.Lang.PVar _id)), exp)
    -> (id, (Expr.mk_let_in _id Type.mk_unit (Expr.Var binder) (convert_expr exp)))
  | ((id, Some (Myth.Lang.PTuple _plist)), exp)
    -> (id, (List.fold
               (explode (Expr.Var binder) _plist)
               ~init:(convert_expr exp)
               ~f:(fun eacc (e, _id) -> Expr.mk_let_in _id Type.mk_unit e eacc)))