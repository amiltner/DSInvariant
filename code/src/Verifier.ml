open Lang

module type t =
sig
  val equiv_false :
    problem:problem ->
    cond:Expr.t ->
    bool

  val implication_counter_example :
    problem:problem ->
    pre:Expr.t ->
    eval:Expr.t ->
    eval_t:Type.t ->
    post:UniversalFormula.t ->
    (Value.t list) option

  val true_on_examples :
    problem:problem ->
    examples:Value.t list ->
    eval:Expr.t ->
    eval_t:Type.t ->
    post:UniversalFormula.t ->
    (Value.t list) option

  val synth :
    problem:problem ->
    testbed:TestBed.t ->
    Expr.t list
end
