open MyStdlib
open OUnitPlusPlus
open DSInvGen
open Myth.Lang

let assert_mythexpr_equal
    (expected:exp)
    (actual:exp) =
  assert_equal
    ~printer:Myth.Pp.pp_exp
    ~cmp:compare_exp
    expected
    actual

let assert_mythtype_equal
    (expected:typ)
    (actual:typ) =
  assert_equal
    ~printer:Myth.Pp.pp_typ
    ~cmp:compare_typ
    expected
    actual
