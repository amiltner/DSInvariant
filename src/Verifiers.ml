type model = (string * Value.t) list

module type Verifier =
sig
  type t
  type exp = t
  val true_exp : t
  val false_exp : t
  val to_string : t -> string
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val and_exps : t -> t -> t
  val implication_counter_example : pre:t -> eval:t -> post:t -> model option
  val from_synth : Value.t list TestBed.feature TestBed.with_desc CNF.t option -> t
  val simplify : t -> t
end

module Z3Verifier =
struct
  let context = Z3.mk_context []

  type t = Z3.Expr.expr
  type exp = t

  let true_exp = Z3.Boolean.mk_true context
  let false_exp = Z3.Boolean.mk_false context
  let to_string = Z3.Expr.to_string
  let compare = Z3.Expr.compare
  let equal = Z3.Expr.equal
  let and_exps e1 e2 = Z3.Boolean.mk_and context [e1;e2]
  let implication_counter_example
      ~pre:(_:t)
      ~eval:(_:t)
      ~post:(_:t)
    : model option =
    failwith "TODO"
  let simplify
      (e:t)
    : t =
    Z3.Expr.simplify e None
  let from_synth
      (_:Value.t list TestBed.feature TestBed.with_desc CNF.t option)
    : t =
    failwith "TODO: uhhhh"
end

let z3_verifier = (module Z3Verifier : Verifier)
