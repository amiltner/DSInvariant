open Lang

module type t = sig
  val synth :
    problem:problem ->
    testbed:TestBed.t ->
    Expr.t option
end
