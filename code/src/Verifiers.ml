open MyStdlib

type model = (string * Value.t) list

module type Verifier =
sig
  type expr
  type t
  type func
  val empty : t
  val true_exp : expr
  val false_exp : expr
  val to_string : expr -> string
  val compare : expr -> expr -> int
  val equal : expr -> expr -> bool
  val bin_and_exps : expr -> expr -> expr
  val make_app : func -> expr list -> expr
  val implication_counter_example : pre:expr -> eval:expr -> post:expr -> v:t -> model option
  val from_synth : Value.t list TestBed.feature TestBed.with_desc CNF.t option -> string
  val simplify : expr -> expr
  val sat_model_for_asserts : eval_term:expr -> db:expr list -> model option
  val integer_var_exp : string -> expr
  val if_then_else_exp : expr -> expr -> expr -> expr
  val register_func : t -> SyGuS_Set.func -> t * func
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

  let _ = Stdio.print_endline (Z3.Expr.to_string delete_func_def);


  type expr = Expr.expr

  type t = (FuncDecl.func_decl list * expr list * Symbol.symbol list)

  type func = FuncDecl.func_decl

  let empty : t = ([],[],[])

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

  let implication_counter_example
      ~pre:(pre:expr)
      ~eval:(eval:expr)
      ~post:(post:expr)
      ~v:(v:t)
    : model option =
    let solver = Solver.mk_simple_solver context in
    let defs = (snd3 v) in
    let g = Goal.mk_goal context false false false in
    let impl = Boolean.mk_not context (Boolean.mk_implies context pre post) in
    Goal.add g (impl::eval::defs);
    (List.iter
       ~f:(fun f -> (Solver.add solver [f]))
       (Goal.get_formulas g));
    Stdio.print_endline "";
    Stdio.print_endline "";
    Stdio.print_endline "";
    Stdio.print_endline "";
    Stdio.print_endline (Solver.to_string solver);
    let ans = Solver.check solver [] in
    begin match ans with
      | SATISFIABLE ->
        let model_option = Solver.get_model solver in
        Option.map
          ~f:(fun model -> Stdio.print_endline (Model.to_string model); [])
          model_option
      | _ -> None
    end

  let simplify
      (e:expr)
    : expr =
    Expr.simplify e None

  let from_synth
      (pred:Value.t list TestBed.feature TestBed.with_desc CNF.t option)
    : string =
      match pred with
      | None -> "false"
      | Some pred -> CNF.to_string pred ~stringify:snd

  let sat_model_for_asserts
      ~eval_term:(_ : expr)
      ~db:(_ : expr list)
      : model option =
    failwith "TODO: ah"

  let integer_var_exp
      (var:string)
    : expr =
    Arithmetic.Integer.mk_const
      context
      (Symbol.mk_string context var)

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

  let var_to_z3_var_intro
      (v:SyGuS_Set.var)
    : string =
    "(" ^ (fst v) ^ " " ^ (Type.to_string @$ snd v) ^ ") "

  let register_func
      ((fs,es,ss):t)
      (f:SyGuS_Set.func)
    : t * func =
    let func_symbol =
      (Symbol.mk_string context f.name)
    in
    let func_decl =
      FuncDecl.mk_func_decl
        context
        func_symbol
        (List.map ~f:(type_to_z3_type % snd) f.args)
        (type_to_z3_type f.return)
    in
    let ss = func_symbol::ss in
    let fs = func_decl::fs in
    let func_def =
      Z3.SMT.parse_smtlib2_string context
        ("(assert (forall "
         ^ (paren (String.concat (List.map ~f:var_to_z3_var_intro f.args)))
         ^ "(= " ^ (paren (f.name ^ " " ^ String.concat ~sep:" " ((List.map ~f:fst f.args)))) ^ f.expr ^ ")"
         ^ "))")
        []
        []
        ss
        fs
    in
    Stdio.print_endline (Expr.to_string func_def);
    let new_t = (fs,func_def::es,ss) in
    (new_t,func_decl)

  let make_app
      (f:func)
      (exs:expr list)
    : expr =
    Expr.mk_app context f exs
end

let z3_verifier = (module Z3Verifier : Verifier)
