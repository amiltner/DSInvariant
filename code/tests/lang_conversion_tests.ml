open MyStdlib
open DSInvGen
open Lang
open OUnitPlusPlus
open Mythlang_asserts

let run_test_tt_main _ = ()

let to_myth_tt =
  DSToMyth.TypeToType.from_kvp_list
    [ (Type.mk_variant [("O", Type.mk_unit); "S", Type.mk_var "nat"], TBase "nat")
    ; (Type.mk_var "nat", TBase "nat")
    ; (Type.mk_var "x", TTuple [TBase "nat"; TBase "nat"])
    ]


(* begin to_myth_type_basic *)
let to_myth_type_basic_unit _ =
  assert_mythtype_equal
    TUnit
    (DSToMyth.to_myth_type_basic
       to_myth_tt
       (Type.mk_unit))

let to_myth_type_basic_var _ =
  assert_mythtype_equal
    (TBase "nat")
    (DSToMyth.to_myth_type_basic
       to_myth_tt
       (Type.mk_var "nat"))

let to_myth_type_basic_var_2 _ =
  assert_mythtype_equal
    (TTuple [TBase "nat"; TBase "nat"])
    (DSToMyth.to_myth_type_basic
       to_myth_tt
       (Type.mk_var "x"))

let to_myth_type_basic_arrow _ =
  assert_mythtype_equal
    (TArr (TBase "nat",TUnit))
    (DSToMyth.to_myth_type_basic
       to_myth_tt
       (Type.mk_arr (Type.mk_var "nat") Type.mk_unit))

let to_myth_type_basic_tuple _ =
  assert_mythtype_equal
    (TTuple [TBase "nat";TUnit])
    (DSToMyth.to_myth_type_basic
       to_myth_tt
       (Type.mk_tuple [Type.mk_var "nat";Type.mk_unit]))

let to_myth_type_basic_variant _ =
  assert_mythtype_equal
    (TBase "nat")
    (DSToMyth.to_myth_type_basic
       to_myth_tt
       (Type.mk_variant [("O", Type.mk_unit); "S", Type.mk_var "nat"]))

let to_myth_type_basic_suite =
  "to_myth_type_basic Unit Tests" >:::
  ["to_myth_type_basic_unit" >:: to_myth_type_basic_unit
  ;"to_myth_type_basic_var" >:: to_myth_type_basic_var
  ;"to_myth_type_basic_var_2" >:: to_myth_type_basic_var_2
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
       to_myth_tt
       Expr.mk_unit)

let to_myth_exp_var _ =
  assert_mythexpr_equal
    (EVar "x")
    (DSToMyth.to_myth_exp
       to_myth_tt
       (Expr.mk_var "x"))

let to_myth_exp_app _ =
  assert_mythexpr_equal
    (EApp ((EVar "f"),(EVar "x")))
    (DSToMyth.to_myth_exp
       to_myth_tt
       (Expr.mk_app (Expr.mk_var "f") (Expr.mk_var "x")))

let to_myth_exp_func _ =
  assert_mythexpr_equal
    (EFun (("x",TBase "nat"), EVar "x"))
    (DSToMyth.to_myth_exp
       to_myth_tt
       (Expr.mk_func ("x",Type.mk_var "nat") (Expr.mk_var "x")))

let to_myth_exp_ctor _ =
  assert_mythexpr_equal
    (ECtor ("S",ECtor ("O",ETuple [])))
    (DSToMyth.to_myth_exp
       to_myth_tt
       (Expr.mk_ctor "S" (Expr.mk_ctor "O" Expr.mk_unit)))

let to_myth_exp_match _ =
  assert_mythexpr_equal
    (EMatch (EVar "x", [(("O", Some (PVar "y")), EVar "y");(("S", Some (PVar "y")), ETuple [])]))
    (DSToMyth.to_myth_exp
       to_myth_tt
       (Expr.mk_match (Expr.mk_var "x") "y" [("O",Expr.mk_var "y");("S",Expr.mk_unit)]))

let to_myth_exp_fix _ =
  assert_mythexpr_equal
    (EFix ("f", ("x", TBase "nat"), TUnit, EVar "y"))
    (DSToMyth.to_myth_exp
       to_myth_tt
       (Expr.mk_fix "f" (Type.mk_arr (Type.mk_var "nat") (Type.mk_unit)) (Expr.mk_func ("x",Type.mk_var "nat") (Expr.mk_var "y"))))

let to_myth_exp_tuple _ =
  assert_mythexpr_equal
    (ETuple [ETuple []; EVar "x"])
    (DSToMyth.to_myth_exp
       to_myth_tt
       (Expr.mk_tuple [Expr.mk_unit; Expr.mk_var "x"]))

let to_myth_exp_proj _ =
  assert_mythexpr_equal
    (EProj (10, EVar "x"))
    (DSToMyth.to_myth_exp
       to_myth_tt
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

(* start convert_decl_list_to_myth *)
let ec =
  ExprContext.from_kvp_list
    [("u",Type.mk_unit)
    ;("i",Type.mk_var "i")
    ;("func",Type.mk_arr (Type.mk_var "i") (Type.mk_var "nat"))]

let convert_decl_list ds = fst @$ DSToMyth.convert_decl_list_to_myth ec ds

let convert_decl_list_to_myth_empty _ =
  assert_decl_list_equal
    []
    (convert_decl_list [])

let convert_decl_list_to_myth_useless_type_decl _ =
  assert_decl_list_equal
    []
    (convert_decl_list [TypeDeclaration ("i",Type.mk_unit)])

let convert_decl_list_to_myth_useful_type_decl _ =
  assert_decl_list_equal
    [DData ("bool",[("True",TUnit);("False",TUnit)])]
    (convert_decl_list
       [TypeDeclaration
          ("bool"
          ,Type.mk_variant [("True",Type.mk_unit);("False",Type.mk_unit)])])

let convert_decl_list_to_myth_mu_type_decl _ =
  assert_decl_list_equal
    [DData ("nat",[("O",TUnit);("S",TBase "nat")])]
    (convert_decl_list
       [TypeDeclaration
          ("nat",
           Type.mk_mu "nat"
             (Type.mk_variant
                [("O",Type.mk_unit);("S",Type.mk_var "nat")]))])

let convert_decl_list_to_myth_simple_let_decl _ =
  assert_decl_list_equal
    [DLet ("u",false,[],TUnit, ETuple [])]
    (convert_decl_list [ExprDeclaration ("u",Expr.mk_unit)])

let convert_decl_list_to_myth_hard_let_decl _ =
  assert_decl_list_equal
    [DLet ("i",false,[],TUnit, ETuple [])]
    (convert_decl_list [TypeDeclaration ("i",Type.mk_unit);ExprDeclaration ("i",Expr.mk_unit)])

let convert_decl_list_to_myth_let_func_decl _ =
  assert_decl_list_equal
    [DData ("nat",[("O",TUnit);("S",TBase "nat")])
    ;DData ("bool",[("True",TUnit);("False",TUnit)])
    ;DLet ("func",false,[],TArr (TUnit,TBase "nat"), EFun (("x",TUnit), ECtor ("O",ETuple [])))
    ]
    (convert_decl_list
       [TypeDeclaration ("i",Type.mk_unit)
       ;TypeDeclaration
           ("nat",
            Type.mk_mu "nat"
              (Type.mk_variant
                 [("O",Type.mk_unit);("S",Type.mk_var "nat")]))
       ;TypeDeclaration ("bool",Type.mk_variant [("True",Type.mk_unit);("False",Type.mk_unit)])
       ;ExprDeclaration ("func",Expr.mk_func ("x",Type.mk_var "i") (Expr.mk_ctor "O" Expr.mk_unit))])


let convert_decl_list_to_myth_suite =
  "convert_decl_list_to_myth Unit Tests" >:::
  ["convert_decl_list_to_myth_empty" >:: convert_decl_list_to_myth_empty
  ;"convert_decl_list_to_myth_useless_type_decl" >:: convert_decl_list_to_myth_useless_type_decl
  ;"convert_decl_list_to_myth_useful_type_decl" >:: convert_decl_list_to_myth_useful_type_decl
  ;"convert_decl_list_to_myth_mu_type_decl" >:: convert_decl_list_to_myth_useful_type_decl
  ;"convert_decl_list_to_myth_simple_let_decl" >:: convert_decl_list_to_myth_simple_let_decl
  ;"convert_decl_list_to_myth_hard_let_decl" >:: convert_decl_list_to_myth_hard_let_decl
  ;"convert_decl_list_to_myth_let_func_decl" >:: convert_decl_list_to_myth_let_func_decl
  ]

let _ = run_test_tt_main convert_decl_list_to_myth_suite
(* end convert_decl_list_to_myth *)
