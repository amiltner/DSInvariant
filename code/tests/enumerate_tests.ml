open MyStdlib
open DSInvGen
open Lang
open Lang_asserts
open OUnitPlusPlus

(* begin type_equiv *)
let enumerate_context =
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

let test_enumerate_unit _ =
  assert_expr_list_equal
    [Expr.mk_unit]
    (EnumerativeVerifier.T.elements_of_type_and_size
       enumerate_context
       Type.mk_unit
       1)

let type_equiv_suite =
  "typecheck_exp Unit Tests" >:::
  ["typecheck_unit" >:: test_enumerate_unit
  ]

let _ = run_test_tt_main type_equiv_suite
(* end typecheck_exp *)
