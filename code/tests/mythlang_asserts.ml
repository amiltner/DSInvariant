open MyStdlib
open OUnitPlusPlus
open DSInvGen
open Myth_folds.Lang

let assert_mythexpr_equal
    (expected:exp)
    (actual:exp) =
  assert_equal
    ~printer:Myth_folds.Pp.pp_exp
    ~cmp:compare_exp
    expected
    actual

let assert_mythtype_equal
    (expected:typ)
    (actual:typ) =
  assert_equal
    ~printer:Myth_folds.Pp.pp_typ
    ~cmp:compare_typ
    expected
    actual

let assert_decl_list_equal
    (expected:decl list)
    (actual:decl list) =
  assert_equal
    ~printer:(string_of_list Myth_folds.Pp.pp_decl)
    ~cmp:(compare_list ~cmp:compare_decl)
    expected
    actual
