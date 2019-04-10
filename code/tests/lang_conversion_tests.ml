open MyStdlib
open DSInvGen
open Lang
open OUnitPlusPlus
open Mythlang_asserts
open Language_conversion



let to_myth_ti =
  DSToMyth.TypeToId.from_kvp_list
    [ (Type.mk_variant [("O", Type.mk_unit); "S", Type.mk_var "nat"], "nat")
    ; (Type.mk_var "nat", "nat")
    ]


(* begin to_myth_type_basic *)
let to_myth_type_basic_unit _ =
  assert_mythtype_equal
    (TTuple [])
    (DSToMyth.to_myth_type_basic
       to_myth_ti
       (Type.mk_unit))

let to_myth_type_basic_var _ =
  assert_mythtype_equal
    (TBase "nat")
    (DSToMyth.to_myth_type_basic
       to_myth_ti
       (Type.mk_var "nat"))

let to_myth_type_basic_arrow _ =
  assert_mythtype_equal
    (TArr (TBase "nat",TTuple []))
    (DSToMyth.to_myth_type_basic
       to_myth_ti
       (Type.mk_arr (Type.mk_var "nat") Type.mk_unit))

let to_myth_type_basic_tuple _ =
  assert_mythtype_equal
    (TTuple [TBase "nat";TTuple []])
    (DSToMyth.to_myth_type_basic
       to_myth_ti
       (Type.mk_tuple [Type.mk_var "nat";Type.mk_unit]))

let to_myth_type_basic_variant _ =
  assert_mythtype_equal
    (TBase "nat")
    (DSToMyth.to_myth_type_basic
       to_myth_ti
       (Type.mk_variant [("O", Type.mk_unit); "S", Type.mk_var "nat"]))

let to_myth_type_basic_suite =
  "to_myth_type_basic Unit Tests" >:::
  ["to_myth_type_basic_unit" >:: to_myth_type_basic_unit
  ;"to_myth_type_basic_var" >:: to_myth_type_basic_var
  ;"to_myth_type_basic_arrow" >:: to_myth_type_basic_arrow
  ;"to_myth_type_basic_tuple" >:: to_myth_type_basic_tuple
  ;"to_myth_type_basic_variant" >:: to_myth_type_basic_variant
  ]

let _ = run_test_tt_main to_myth_type_basic_suite
(* end to_myth_type_basic *)




(* begin to_myth_exp *)
let to_myth_exp_unit _ =
  assert_mythexpr_equal
    (ETuple [])
    (DSToMyth.to_myth_exp
       to_myth_ti
       Expr.mk_unit)

let to_myth_exp_var _ =
  assert_mythexpr_equal
    (EVar "x")
    (DSToMyth.to_myth_exp
       to_myth_ti
       (Expr.mk_var "x"))

let to_myth_exp_app _ =
  assert_mythexpr_equal
    (EApp ((EVar "f"),(EVar "x")))
    (DSToMyth.to_myth_exp
       to_myth_ti
       (Expr.mk_app (Expr.mk_var "f") (Expr.mk_var "x")))

let to_myth_exp_func _ =
  assert_mythexpr_equal
    (EFun (("x",TBase "nat"), EVar "x"))
    (DSToMyth.to_myth_exp
       to_myth_ti
       (Expr.mk_func ("x",Type.mk_var "nat") (Expr.mk_var "x")))

let to_myth_exp_ctor _ =
  assert_mythexpr_equal
    (ECtor ("S",ECtor ("O",ETuple [])))
    (DSToMyth.to_myth_exp
       to_myth_ti
       (Expr.mk_ctor "S" (Expr.mk_ctor "O" Expr.mk_unit)))

let to_myth_exp_match _ =
  assert_mythexpr_equal
    (EMatch (EVar "x", [(("O", Some (PVar "y")), EVar "y");(("S", Some (PVar "y")), ETuple [])]))
    (DSToMyth.to_myth_exp
       to_myth_ti
       (Expr.mk_match (Expr.mk_var "x") "y" [("O",Expr.mk_var "y");("S",Expr.mk_unit)]))

let to_myth_exp_fix _ =
  assert_mythexpr_equal
    (EFix ("f", ("x", TBase "nat"), TTuple [], EVar "y"))
    (DSToMyth.to_myth_exp
       to_myth_ti
       (Expr.mk_fix "f" (Type.mk_arr (Type.mk_var "nat") (Type.mk_unit)) (Expr.mk_func ("x",Type.mk_var "nat") (Expr.mk_var "y"))))

let to_myth_exp_tuple _ =
  assert_mythexpr_equal
    (ETuple [ETuple []; EVar "x"])
    (DSToMyth.to_myth_exp
       to_myth_ti
       (Expr.mk_tuple [Expr.mk_unit; Expr.mk_var "x"]))

let to_myth_exp_proj _ =
  assert_mythexpr_equal
    (EProj (10, EVar "x"))
    (DSToMyth.to_myth_exp
       to_myth_ti
       (Expr.mk_proj 9 (Expr.mk_var "x")))



let to_myth_type_basic_suite =
  "to_myth_exp_var Unit Tests" >:::
  ["to_myth_exp_unit" >:: to_myth_exp_unit
  ;"to_myth_exp_var" >:: to_myth_exp_var
  ;"to_myth_exp_app" >:: to_myth_exp_app
  ;"to_myth_exp_func" >:: to_myth_exp_func
  ;"to_myth_exp_ctor" >:: to_myth_exp_ctor
  ;"to_myth_exp_match" >:: to_myth_exp_match
  ;"to_myth_exp_fix" >:: to_myth_exp_fix
  ;"to_myth_exp_tuple" >:: to_myth_exp_tuple
  ;"to_myth_exp_proj" >:: to_myth_exp_proj
  ]

let _ = run_test_tt_main to_myth_type_basic_suite
(* end to_myth_exp *)
