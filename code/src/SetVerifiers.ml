open MyStdlib
open Utils

type model = (string * Value.t) list

module type Verifier =
sig
  type expr
  val true_exp : expr
  val alternative_true_exp : expr
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
  val mk_let_in : string -> expr -> expr -> expr
  val mk_lt : expr -> expr -> expr
  val mk_le : expr -> expr -> expr
  val mk_not : expr -> expr
  val mk_or : expr list -> expr
  val implication_counter_example : resultant:bool -> pre:expr -> eval:expr -> post:expr -> Value.t option -> model option
  val true_on_examples : examples:expr list -> post:expr -> model option
  val synth : consts:Value.t list -> NonModuleTestBed.t -> expr option
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

module QuickCheckVerifier =
struct
  open Myth
  open Sigma
  open Lang
  type expr = exp

  type t = Sigma.t

  (*let bool_sigma =
    Sigma.make_from_data
      "bool"
      [("True",TUnit)
      ;("False",TUnit)]

  let nat_sigma =
    Sigma.make_from_data
      "nat"
      [("O",TUnit)
      ;("S",TBase "nat")]

  let list_sigma =
    Sigma.make_from_data
      "intlist"
      [("Nil",TUnit)
      ;("Cons",TTuple [TBase "nat";TBase "intlist"])]

  let sigma =
    Sigma.append
      bool_sigma
      (Sigma.append
         nat_sigma
         list_sigma)*)

  let real_true_exp : expr = 
    ECtor ("True",EUnit)

  let true_exp : expr =
    let true_prei = EFix ("f1",("l1",TBase "list"),TBase "bool",EApp (EVar "not", ECtor ("False",EUnit))) in
    EFun (("i1",TBase "nat"), true_prei)

  let alternative_true_exp : expr =
    let true_prei = EFix ("f1",("l1",TBase "list"),TBase "bool",ECtor ("True",EUnit)) in
    EFun (("i1",TBase "nat"), true_prei)

  let is_true
      (v:value)
    : bool =
    match v with
    | VCtor ("True",VUnit) -> true
    | _ -> false

  let compare = compare_exp

  let initial_context =
    "
type bool =
  | True
  | False

type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

type cmp =
  | LT
  | EQ
  | GT

let rec compare (n1 : nat) (n2 :nat) : cmp =
  match n1 with
  | O -> ( match n2 with 
           | O -> EQ
           | S m -> LT
         )
  | S m1 -> 
      ( match n2 with
      | O -> GT
      | S m2 -> (compare m1 m2) )
;;

let rec and (b1:bool) (b2:bool) : bool =
  match b1 with
  | True -> b2
  | False -> False
;;

let rec or (b1:bool) (b2:bool) : bool =
  match b1 with
  | True -> True
  | False -> b2
;;

let rec not (b:bool) : bool =
  match b with
  | True -> False
  | False -> True
;;

let rec empty (i1:nat) (l1:list) : bool =
  match l1 with
  | Nil -> True
  | Cons (i2,l2) -> False
;;

let insert (i1:nat) : list -> list =
      let rec insert (l1:list) : list =
  match l1 with
  | Nil -> Cons(i1,Nil)
  | Cons(i2,l2) -> (match compare i1 i2 with
                    | LT -> l1
                    | EQ -> l1
                    | GT -> Cons(i2,insert l2))
      in
      insert
;;

let rec delete (i1:nat) : list -> list =
 let rec delete (l1:list) : list =
  match l1 with
  | Nil -> Nil
  | Cons(i2,l2) -> (match compare i1 i2 with
                    | LT -> l1
                    | EQ -> l2
                    | GT -> Cons(i2,delete l2))
      in
      delete
;;

let rec lookup (i1:nat) : list -> bool =
      let rec lookup (l1:list) : bool =
  match l1 with
  | Nil -> False
  | Cons(i2,l2) -> (match compare i1 i2 with
                    | LT -> False
                    | EQ -> True
                    | GT -> lookup l2)
      in
      lookup
;;

let rec precond (i1:nat) (l1:list) : list =
  l1
;;

let rec post (i1:nat) (l1:list) : bool =
  not (lookup i1 (delete i1 l1))
;;

let rec append (l1:list) (l2:list) : list =
  match l1 with
  | Nil -> l2
  | Cons (hd, tl) -> Cons (hd, append tl l2)
;;

let concat : list -> list |>
  { LNil => []
  | LCons ([], LNil) => []
  | LCons ([0], LNil) => [0]
  | LCons ([0], LCons([0], LNil)) => [0;0]
  | LCons ([1], LNil) => [1]
  | LCons ([1], LCons([1], LNil)) => [1;1]
  } = ?
"

  let synth_context =
    "
type bool =
  | True
  | False

type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

type cmp =
  | LT
  | EQ
  | GT

let rec compare (n1 : nat) (n2 :nat) : cmp =
  match n1 with
  | O -> ( match n2 with 
           | O -> EQ
           | S m -> LT
         )
  | S m1 -> 
      ( match n2 with
      | O -> GT
      | S m2 -> (compare m1 m2) )
;;

let rec and (b1:bool) (b2:bool) : bool =
  match b1 with
  | True -> b2
  | False -> False
;;

let rec or (b1:bool) (b2:bool) : bool =
  match b1 with
  | True -> True
  | False -> b2
;;

let rec not (b:bool) : bool =
  match b with
  | True -> False
  | False -> True
;;

let concat : list -> list |>
  { LNil => []
  | LCons ([], LNil) => []
  | LCons ([0], LNil) => [0]
  | LCons ([0], LCons([0], LNil)) => [0;0]
  | LCons ([1], LNil) => [1]
  | LCons ([1], LCons([1], LNil)) => [1;1]
  } = ?
"

  let (decls,_) = Parser.prog Lexer.token (Lexing.from_string initial_context)
  let (synthdecls,_) = Parser.prog Lexer.token (Lexing.from_string synth_context)

  let (sigma,gamma) =
    Typecheck.Typecheck.check_decls
      Sigma.empty
      Gamma.Gamma.empty
      decls

  let (synthsigma,synthgamma) =
    Typecheck.Typecheck.check_decls
      Sigma.empty
      Gamma.Gamma.empty
      synthdecls

  let env = Eval.gen_init_env decls
  let synthenv = Eval.gen_init_env synthdecls

  let bin_and_exps e1 e2 =
    let i1_var = EVar("i1") in
    let l1_var = EVar("l1") in
    let apped_e1 = EApp (EApp (e1,i1_var), l1_var) in
    let apped_e2 = EApp (EApp (e2,i1_var), l1_var) in
    EFun (("i1",TBase ("nat")),
          EFun (("l1",TBase ("list")),
                EApp (EApp (EVar "and",apped_e1), apped_e2)))

  let and_exps es =
    fold_on_head_exn
      ~f:(fun acc x -> bin_and_exps acc x)
      es

  let get_snd
      (p:expr)
    : expr =
    EApp (EVar "snd", p)

  let get_fst
      (p:expr)
    : expr =
    EApp (EVar "fst", p)

  let mk_equals
      (e1:expr)
      (e2:expr)
    : expr =
    EApp (EApp (EVar "eq",e1), e2)

  let mk_lt
    (e1:expr)
    (e2:expr)
    : expr =
    EApp (EApp (EVar "lt",e1), e2)

  let mk_le
      (e1:expr)
      (e2:expr)
    : expr =
    EApp (EApp (EVar "le",e1), e2)

  let mk_not
      (e:expr)
    : expr =
    EApp (EVar "not", e)

  let mk_or
      (es:expr list)
    : expr =
    fold_on_head_exn
      ~f:(fun acc x -> EApp (EApp (EVar "or",acc), x))
      es

  let make_pair
    (x:expr)
    (y:expr)
    : expr =
    ETuple [x;y]

  let integer_var_exp
      (var:string)
    : expr =
    EVar var

  let rec to_int_expr
      (i:int)
    : expr =
    if i = 0 then
      ECtor("O", EUnit)
    else
      ECtor("S", to_int_expr (i-1))


  let to_int_list_expr
      (is:int list)
    : expr =
    List.fold_right
      ~f:(fun i acc ->
          ECtor("Cons",ETuple [to_int_expr i;acc]))
      ~init:(ECtor("Nil",EUnit))
      is

  let mk_app
      (e1:expr)
      (e2:expr)
    : expr =
    EApp(e1,e2)

  let evaluate
      (e:expr)
    : value =
    Eval.eval env e

  let to_value
      (e:expr)
    : Value.t option =
    let rec val_to_value
        (v:value)
      : Value.t option =
      begin match v with
        | VCtor ("O",_) -> Some (Int 0)
        | VCtor ("S",v') ->
          begin match val_to_value v' with
            | Some (Int i) -> Some (Int (i+1))
            | _ -> None
          end
        | VCtor ("True",_) -> Some (Bool true)
        | VCtor ("False",_) -> Some (Bool false)
        | VCtor ("Nil",_) -> Some (IntList [])
        | VCtor ("Cons",v') ->
          begin match v' with
            | VTuple [v1;v2] ->
              begin match (val_to_value v1, val_to_value v2) with
                | (Some (Int i), Some IntList l) -> Some (IntList (i::l))
                | _ -> None
              end
            | _ -> None
          end
        | _ -> None
      end
    in
    val_to_value (Eval.eval env e)

  let to_value_exn
      (e:expr)
    : Value.t =
    Option.value_exn (to_value e)

  let implication_counter_example
      ~resultant:(resultant:bool)
      ~pre:(pre:expr)
      ~eval:(eval:expr)
      ~post:(post:expr)
      (mylist:Value.t option)
    : model option =
    let intlist_generator =
      Quickcheck.Generator.list Quickcheck.Generator.small_non_negative_int
    in
    let intlist_seq = Quickcheck.random_sequence intlist_generator in
    let int_seq = Quickcheck.random_sequence Quickcheck.Generator.small_non_negative_int in
    let ce_option =
      List.fold_left
        ~f:(fun (int_seq,intlist_seq,ce_option) _ ->
            begin match ce_option with
              | None ->
                let (l,intlist_seq) = Option.value_exn (Sequence.next intlist_seq) in
                let l =
                  begin match mylist with
                    | None -> l
                    | Some IntList l -> l
                    | _ -> failwith "nope"
                  end
                in
                let (i1,int_seq) = Option.value_exn (Sequence.next int_seq) in
                let (i2,int_seq) = Option.value_exn (Sequence.next int_seq) in
                let (i3,int_seq) = Option.value_exn (Sequence.next int_seq) in
                let apped_pre =
                  (mk_app
                     (mk_app pre (to_int_expr i1))
                     (to_int_list_expr l))
                in
                (*print_endline @$ "PRECOND:" ^ (Pp.pp_exp apped_pre);*)
                if is_true (evaluate apped_pre)then
                  let evaled =
                    (mk_app
                       (mk_app eval (to_int_expr i2))
                       (to_int_list_expr l))
                  in
                  (*print_endline @$ "TRUEPRECOND:";*)
                  let post =
                    (mk_app
                       (mk_app post (to_int_expr i3))
                       evaled)
                  in
                  (*print_endline @$ "POSTCOND:" ^ (Pp.pp_exp post);*)
                  if not @$ is_true (evaluate post) then
                    ((*print_endline "falsepostcond";*) int_seq,intlist_seq,if resultant then Some (to_value_exn evaled) else Some (IntList l))
                  else
                    ((*print_endline "truepostcond"; *)int_seq,intlist_seq,None)
                else
                  ((*print_endline "FALSEPRECOND";*) int_seq,intlist_seq,None)
              | Some ce -> (int_seq,intlist_seq,Some ce)
            end)
        ~init:(int_seq,intlist_seq,None)
        (range 0 100)
    in
    match trd3 ce_option with
    | None -> None
    | Some ce -> Some [("x",ce)]

  let true_on_examples
      ~examples:(_:expr list)
      ~post:(_:expr)
    : model option =
    failwith "TODO"

  let simplify
      (e:expr)
    : expr =
    e

  let substitute
      (e:expr)
      (_:expr list)
      (_:expr list)
    : expr =
    e
  (*failwith "cannot do"*)
    (*Expr.substitute
      e
      old_es
      new_es*)

  let sat_model_for_asserts
      ~eval_term:(_ : expr)
      ~db:(_ : expr list)
      : model option =
    failwith "TODO: ah"

  let integer_exp
      (i:int)
    : expr =
    if i < 0 then
      failwith ("cannot" ^ (string_of_int i))
    else
      to_int_expr i

  let bool_exp
      (b:bool)
    : expr =
    let str = if b then "True" else "False" in
    ECtor(str,EUnit)

  let if_then_else_exp
      (cond:expr)
      (if_branch:expr)
      (else_branch:expr)
    : expr =
    EMatch
      (cond
      ,[(("True",None),if_branch)
       ;(("False",None),else_branch)])

  let from_value
      (v:Value.t)
    : expr =
    begin match v with
      | Int i -> integer_exp i
      | Bool b -> bool_exp b
      | IntList is -> to_int_list_expr is
    end

  let false_exp
    : expr =
    ECtor ("False",EUnit)

  let to_string
      (e:expr)
    : string =
    Pp.pp_exp e

  let equal
      (e1:expr)
      (e2:expr)
    : bool =
    e1 = e2

  let synth
      ~consts:(_:Value.t list)
      (tb:NonModuleTestBed.t)
    : expr option =
    let pos_examples = List.map ~f:(fun (v,_) -> (from_value (List.hd_exn v),real_true_exp)) tb.pos_tests in
    let neg_examples = List.map ~f:(fun (v,_) -> (from_value (List.hd_exn v),false_exp)) tb.neg_tests in
    let w = Eval.gen_init_world synthenv [EPFun (pos_examples@neg_examples)] in
    let listfun = Synth.synthesize sigma synthenv (Rtree.create_rtree sigma synthgamma synthenv (TArr (TBase "list",TBase "bool")) w 0) in
    Option.map ~f:(fun lf -> EFun (("i1",TBase "nat"), lf)) listfun

  let mk_let_in
      (s:string)
      (e1:expr)
      (e2:expr)
    : expr =
    ELet (s,false,[],TBase "list", e1, e2)
end

let quickcheck_verifier = (module QuickCheckVerifier : Verifier)
