module type t = sig
  val synth :
    problem:Problem.t ->
    testbed:TestBed.t ->
    Expr.t list
end
