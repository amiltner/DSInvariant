open MyStdlib

type model = (string * Value.t) list

module type Verifier =
sig
  type expr
  val true_exp : expr
  val false_exp : expr
  val to_string : expr -> string
  val compare : expr -> expr -> int
  val equal : expr -> expr -> bool
  val bin_and_exps : expr -> expr -> expr
  val and_exps : expr list -> expr
  val make_pair : expr -> expr -> expr
  val get_fst : expr -> expr
  val get_snd : expr -> expr
  val mk_equals : expr -> expr -> expr
  val mk_lt : expr -> expr -> expr
  val mk_le : expr -> expr -> expr
  val mk_not : expr -> expr
  val mk_or : expr list -> expr
  val implication_counter_example : pre:expr -> eval:expr -> post:expr -> model option
  val from_synth : Value.t list TestBed.feature TestBed.with_desc CNF.t option -> expr
  val simplify : expr -> expr
  val substitute : expr -> expr list -> expr list -> expr
  val sat_model_for_asserts : eval_term:expr -> db:expr list -> model option
  val integer_var_exp : string -> expr
  val integer_exp : int -> expr
  val bool_exp : bool -> expr
  val if_then_else_exp : expr -> expr -> expr -> expr
  val to_value : expr -> Value.t option
  val from_value : Value.t -> expr
  val to_value_exn : expr -> Value.t
end

module Z3Verifier =
struct
  open Z3

  let context = mk_context []

  let int_sort = Arithmetic.Integer.mk_sort context
  let bool_sort = Boolean.mk_sort context

  (*INSERT*)
  let insert_func_symbol =
    (Symbol.mk_string context "insert")
  let insert_func_decl =
    FuncDecl.mk_func_decl
      context
      insert_func_symbol
      [int_sort;int_sort;int_sort;int_sort;int_sort]
      bool_sort
  let insert_func_def =
    Z3.SMT.parse_smtlib2_string context
      "(assert (forall ((x Int) (y Int) (z Int) (x! Int) (y! Int)) (= (insert x y z x! y!) (and (= x! (ite (<= z x) z x)) (= y! (ite (<= z x) y z))))))"
      []
      []
      [insert_func_symbol]
      [insert_func_decl]

  (*LOOKUP*)
  let lookup_func_symbol =
    (Symbol.mk_string context "lookup")
  let lookup_func_decl =
    FuncDecl.mk_func_decl
      context
      lookup_func_symbol
      [int_sort;int_sort;int_sort]
      bool_sort
  let lookup_func_def =
    Z3.SMT.parse_smtlib2_string context
      "(assert (forall ((x Int) (y Int) (z Int)) (= (lookup x y z) (or (= z x) (= z y)))))"
      []
      []
      [lookup_func_symbol]
      [lookup_func_decl]

  (*DELETE*)
  let delete_func_symbol =
    (Symbol.mk_string context "delete")
  let delete_func_decl =
    FuncDecl.mk_func_decl
      context
      delete_func_symbol
      [int_sort;int_sort;int_sort;int_sort;int_sort]
      bool_sort
  let delete_func_def =
    Z3.SMT.parse_smtlib2_string context
      "(assert (forall ((x Int) (y Int) (z Int) (x! Int) (y! Int)) (= (delete x y z x! y!) (and (= x! (ite (< z x) x (ite (= z x) y x))) (= y! (ite (< z x) y (ite (= z x) 2147483647 (ite (= z y) 2147483647 y))))))))"
      []
      []
      [delete_func_symbol]
      [delete_func_decl]

  let invariant_func_symbol =
    (Symbol.mk_string context "invariant")
  let invariant_func_decl =
    FuncDecl.mk_func_decl
      context
      invariant_func_symbol
      [int_sort;int_sort]
      bool_sort

  type expr = Expr.expr

  type t = (FuncDecl.func_decl list * expr list * Symbol.symbol list)

  type func = FuncDecl.func_decl

  let empty : t = ([],[],[])

  let to_value
      (e:expr)
    : Value.t option =
    if Arithmetic.is_int e then
      Some (Int (Arithmetic.Integer.get_int e))
    else
      begin match Boolean.get_bool_value e with
        | L_FALSE -> Some (Bool false)
        | L_TRUE -> Some (Bool true)
        | L_UNDEF -> None
      end

  let to_value_exn
    (e:expr)
    : Value.t =
    Option.value_exn (to_value e)

  let insert_call
      (insert_arg_1_1:expr)
      (insert_arg_1_2:expr)
      (insert_arg_2:expr)
      (insert_res_1:expr)
      (insert_res_2:expr)
    : expr =
    Expr.mk_app
      context
      insert_func_decl
      [insert_arg_1_1
      ;insert_arg_1_2
      ;insert_arg_2
      ;insert_res_1
      ;insert_res_2]

  let lookup_call
      (lookup_arg_1_1:expr)
      (lookup_arg_1_2:expr)
      (lookup_arg_2:expr)
    : expr =
    Expr.mk_app
      context
      lookup_func_decl
      [lookup_arg_1_1
      ;lookup_arg_1_2
      ;lookup_arg_2]

  let true_exp = Boolean.mk_true context

  let false_exp = Boolean.mk_false context

  let to_string = Expr.to_string

  let compare = Expr.compare

  let equal = Expr.equal

  let and_exps es = Boolean.mk_and context es

  let bin_and_exps e1 e2 = Boolean.mk_and context [e1;e2]

  let pair_constructor =
    let pair_constructor =
      Datatype.mk_constructor
        context
        (Symbol.mk_string context "mk-pair")
        (Symbol.mk_string context "mk-pair")
        [Symbol.mk_string context "first";Symbol.mk_string context "second"]
        [Some (Arithmetic.Integer.mk_sort context);Some (Arithmetic.Integer.mk_sort context)]
        [1;2]
    in
    let _ =
      Datatype.mk_sort_s
        context
        "Pair"
        [pair_constructor]
    in
    pair_constructor

  let get_snd
      (p:expr)
    : expr =
    let accessor_decls =
      Datatype.Constructor.get_accessor_decls
        pair_constructor
    in
    let fst = List.nth_exn accessor_decls 1 in
    Expr.mk_app
      context
      fst
      [p]

  let get_fst
      (p:expr)
    : expr =
    let _ =
      Datatype.mk_sort_s
        context
        "Pair"
        [pair_constructor]
    in
    let accessor_decls =
      Datatype.Constructor.get_accessor_decls
        pair_constructor
    in
    let fst = List.nth_exn accessor_decls 0 in
    Expr.mk_app
      context
      fst
      [p]

  let mk_equals
      (e1:expr)
      (e2:expr)
    : expr =
    Boolean.mk_eq context e1 e2

  let mk_lt
    : expr -> expr -> expr =
    Arithmetic.mk_lt context

  let mk_le
    : expr -> expr -> expr =
    Arithmetic.mk_le context

  let mk_not : expr -> expr = Boolean.mk_not context

  let mk_or
      (es:expr list)
    : expr =
    Boolean.mk_or context es

  let make_pair
    (x:expr)
    (y:expr)
    : expr =
    let pair_constructor =
      Datatype.mk_constructor
        context
        (Symbol.mk_string context "mk-pair")
        (Symbol.mk_string context "mk-pair")
        [Symbol.mk_string context "first";Symbol.mk_string context "second"]
        [Some (Arithmetic.Integer.mk_sort context);Some (Arithmetic.Integer.mk_sort context)]
        [1;2]
    in
    let _ =
      Datatype.mk_sort_s
        context
        "Pair"
        [pair_constructor]
    in
    let pair_constructor_function =
      Datatype.Constructor.get_constructor_decl
        pair_constructor
    in
    Expr.mk_app
      context
      pair_constructor_function
      [x;y]

  let integer_var_exp
      (var:string)
    : expr =
    Arithmetic.Integer.mk_const
      context
      (Symbol.mk_string context var)

  let implication_counter_example
      ~pre:(pre:expr)
      ~eval:(eval:expr)
      ~post:(post:expr)
    : model option =
    let solver = Solver.mk_simple_solver context in
    let g = Goal.mk_goal context false false false in
    let impl = Boolean.mk_not context (Boolean.mk_implies context pre post) in
    Goal.add g (impl::eval::[]);
    (List.iter
       ~f:(fun f -> (Solver.add solver [f]))
       (Goal.get_formulas g));
    let ans = Solver.check solver [] in
    begin match ans with
      | SATISFIABLE ->
        let model_option = Solver.get_model solver in
        Option.map
          ~f:(fun model ->
               List.map
                 ~f:(fun fd ->
                     (Symbol.get_string @$ FuncDecl.get_name fd
                     ,to_value_exn @$ Option.value_exn (Model.get_const_interp model fd)))
                 (Model.get_const_decls model))
          model_option
      | _ -> None
    end

  let simplify
      (e:expr)
    : expr =
    Expr.simplify e None

  let substitute
      (e:expr)
      (old_es:expr list)
      (new_es:expr list)
    : expr =
    Expr.substitute
      e
      old_es
      new_es

  let from_synth
      (pred:Value.t list TestBed.feature TestBed.with_desc CNF.t option)
    : expr =
    let from_synth_string =
      begin match pred with
        | None -> "false"
        | Some pred -> CNF.to_string pred ~stringify:snd
      end
    in
    Z3.SMT.parse_smtlib2_string
      context
      ("(declare-const x Int) (declare-const y Int) (assert " ^ from_synth_string ^ ")")
      []
      []
      []
      []

  let sat_model_for_asserts
      ~eval_term:(_ : expr)
      ~db:(_ : expr list)
      : model option =
    failwith "TODO: ah"

  let integer_exp
      (i:int)
    : expr =
    Z3.Arithmetic.Integer.mk_numeral_i context i

  let bool_exp
      (b:bool)
    : expr =
    Z3.Boolean.mk_val context b

  let exp_to_string = Z3.Expr.to_string

  let if_then_else_exp
      (cond:expr)
      (if_branch:expr)
      (else_branch:expr)
    : expr =
    Boolean.mk_ite
      context
      cond
      if_branch
      else_branch

  let type_to_z3_type
      (t:Type.t)
    : Sort.sort =
    begin match t with
      | INT -> Z3.Arithmetic.Integer.mk_sort context
      | BOOL -> Z3.Boolean.mk_sort context
    end

  let make_app
      (f:func)
      (exs:expr list)
    : expr =
    Expr.mk_app context f exs

  let from_value
      (v:Value.t)
    : expr =
    begin match v with
      | Int i -> integer_exp i
      | Bool b -> bool_exp b
    end
end

let z3_verifier = (module Z3Verifier : Verifier)
