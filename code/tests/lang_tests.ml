open MyStdlib
open DSInvGen
open Lang
open Lang_asserts
open OUnit2
open OUnitPlusPlus

(* begin type_equiv *)
let type_equiv_context =
  TypeContext.from_kvp_list
    [("E",Type.mk_tuple [])
    ;("Int"
     ,Type.mk_mu
         "IntInternal"
         (Type.mk_variant[("O",Type.mk_tuple [])
                         ;("S",Type.mk_var "IntInternal")]))
    ;("List"
     ,Type.mk_mu
         "List"
         (Type.mk_variant[("Nil",Type.mk_tuple [])
                         ;("Cons",Type.mk_tuple [Type.mk_var "Int"
                                                ;Type.mk_var "List"])])
     )]

let test_type_equiv_unit _ =
  assert_true
    (either_left_exn
       (Typecheck.type_equiv
          type_equiv_context
          (Type.mk_tuple [])
          (Type.mk_tuple [])))

let test_type_equiv_var_concrete _ =
  assert_true
    (either_left_exn
       (Typecheck.type_equiv
          type_equiv_context
          (Type.mk_var "E")
          (Type.mk_tuple [])))

let test_type_equiv_var_var _ =
  assert_true
    (either_left_exn
       (Typecheck.type_equiv
          type_equiv_context
          (Type.mk_var "E")
          (Type.mk_var "E")))

let test_type_equiv_mu _ =
  assert_true
    (either_left_exn
       (Typecheck.type_equiv
          type_equiv_context
          (Type.mk_var "Int")
          (Type.mk_var "Int")))

let test_type_equiv_mu_unfolded _ =
  let unfolded =
    (Type.mk_variant[("O",Type.mk_tuple [])
                    ;("S",Type.mk_var "IntInternal")])
  in
  assert_true
    (either_left_exn
       (Typecheck.type_equiv
          type_equiv_context
          (Type.mk_var "Int")
          unfolded))

let test_type_equiv_mu_shadow _ =
  assert_true
    (either_left_exn
       (Typecheck.type_equiv
          type_equiv_context
          (Type.mk_var "List")
          (Type.mk_var "List")))

let test_type_equiv_mu_shadow_unfolded _ =
  let unfolded = Type.mk_variant[("Nil",Type.mk_tuple [])
                                 ;("Cons",Type.mk_tuple [Type.mk_var "Int"; Type.mk_var "List"])] in
  assert_true
    (either_left_exn
       (Typecheck.type_equiv
          type_equiv_context
          (Type.mk_var "List")
          unfolded))

let type_equiv_suite =
  "type_equiv Unit Tests" >:::
  ["test_type_equiv_unit" >:: test_type_equiv_unit
  ;"test_type_equiv_var_concrete" >:: test_type_equiv_var_concrete
  ;"test_type_equiv_var_var" >:: test_type_equiv_var_var
  ;"test_type_equiv_mu" >:: test_type_equiv_mu
  ;"test_type_equiv_mu_unfolded" >:: test_type_equiv_mu_unfolded
  ;"test_type_equiv_mu_shadow" >:: test_type_equiv_mu_shadow
  ;"test_type_equiv_mu_shadow_unfolded" >:: test_type_equiv_mu_shadow_unfolded
  ]

let _ = run_test_tt_main type_equiv_suite
(* end type_equiv *)





(* begin typecheck_exp *)
let typecheck_ec =
  ExprContext.from_kvp_list
    [("e1",Type.mk_tuple [])
    ;("e2",Type.mk_var "E")
    ;("i1",Type.mk_mu
        "IntInternal"
        (Type.mk_variant[("O",Type.mk_tuple [])
                        ;("S",Type.mk_var "IntInternal")]))
    ;("i2",Type.mk_var "Int")
    ]

let typecheck_tc =
  TypeContext.from_kvp_list
    [("E",Type.mk_tuple [])
    ;("Int"
     ,Type.mk_mu
         "IntInternal"
         (Type.mk_variant[("O",Type.mk_tuple [])
                         ;("S",Type.mk_var "IntInternal")]))
    ;("List"
     ,Type.mk_mu
         "List"
         (Type.mk_variant[("Nil",Type.mk_tuple [])
                         ;("Cons",Type.mk_tuple [Type.mk_var "Int"
                                                ;Type.mk_var "List"])])
     )]

let typecheck_vc =
  VariantContext.from_kvp_list
    [("O",[("O",Type.mk_tuple []) ;("S",Type.mk_var "IntInternal")])
    ;("S",[("O",Type.mk_tuple []) ;("S",Type.mk_var "IntInternal")])
    ;("Nil",[("Nil",Type.mk_tuple [])
            ;("Cons",Type.mk_tuple [Type.mk_var "Int"; Type.mk_var "List"])])
    ;("Cons",[("Nil",Type.mk_tuple [])
            ;("Cons",Type.mk_tuple [Type.mk_var "Int"; Type.mk_var "List"])])]

let typecheck_unit _ =
  assert_type_equal
    (Type.mk_tuple [])
    (either_left_exn
       (Typecheck.typecheck_exp
          typecheck_ec
          typecheck_tc
          typecheck_vc
          (Expr.tuple [])))

let typecheck_app _ =
  assert_type_equal
    (Type.mk_tuple [])
    (either_left_exn
       (Typecheck.typecheck_exp
          typecheck_ec
          typecheck_tc
          typecheck_vc
          (Expr.app
             (Expr.func ("x",Type.Tuple []) (Expr.var "x"))
             (Expr.tuple []))))

let typecheck_proj_tuple _ =
  assert_type_equal
    (Type.mk_var "Int")
    (either_left_exn
       (Typecheck.typecheck_exp
          typecheck_ec
          typecheck_tc
          typecheck_vc
          (Expr.proj 0 (Expr.tuple [Expr.var "i2";Expr.var "e1"]))))

let type_equiv_suite =
  "typecheck_exp Unit Tests" >:::
  ["typecheck_unit" >:: typecheck_unit
  ;"typecheck_app" >:: typecheck_app
  ;"typecheck_proj_tuple" >:: typecheck_proj_tuple;
  ]

let _ = run_test_tt_main type_equiv_suite
(* end typecheck_exp *)
