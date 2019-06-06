open Core

type t =
  Param.t list * Expr.t
[@@deriving bin_io, eq, hash, ord, sexp, show]
