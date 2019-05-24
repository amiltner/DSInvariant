open MyStdlib
open OUnitPlusPlus
open DSInvGen
open Lang

let assert_expr_equal
    (expected:Expr.t)
    (actual:Expr.t) =
  assert_equal
    ~printer:Expr.show
    ~cmp:Expr.compare
    expected
    actual

let assert_expr_list_equal
    (expected:Expr.t list)
    (actual:Expr.t list) =
  assert_equal
    ~printer:(string_of_list Expr.show)
    ~cmp:(compare_list ~cmp:Expr.compare)
    expected
    actual

let assert_type_equal
    (expected:Type.t)
    (actual:Type.t) =
  assert_equal
    ~printer:Type.show
    ~cmp:Type.compare
    expected
    actual
