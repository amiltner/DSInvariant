open Core

open Lang

type t_unprocessed =
  Declaration.t list * ModuleImplementation.t * ModuleSpec.t * UniversalFormula.t * Type.t option
[@@deriving bin_io, eq, hash, ord, sexp]

type t = {
  module_type  : Type.t                 ;
  ec           : ExprContext.t          ;
  tc           : TypeContext.t          ;
  vc           : VariantContext.t       ;
  mod_vals     : (Expr.t * Type.t) list ;
  post         : UniversalFormula.t     ;
  eval_context : (Id.t * Expr.t) list   ;
  unprocessed  : t_unprocessed          ;
  accumulator  : Type.t option          ;
}
[@@deriving bin_io, eq, hash, make, ord, sexp]
