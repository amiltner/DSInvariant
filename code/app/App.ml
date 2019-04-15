open DSInvGen
open MyStdlib

let _ = Log.enable (Some "log")

  let problem_string =
    "
type nat =
  mu nat.
  | O
  | S of nat

type bool =
  | True
  | False

type list =
  mu list .
  | Nil
  | Cons of (nat * list)

type cmp =
  | LT
  | EQ
  | GT

let compare =
  fix (compare : nat -> nat -> cmp) =
    fun (x1 : nat) ->
      fun (x2 : nat) ->
        match x1 binding x1 with
          | O -> (match x2 binding x2 with
                 | O -> EQ
                 | S -> LT)
          | S -> (match x2 binding x2 with
                 | O -> GT
                 | S -> (compare x1) x2);;

let not =
  fun (v : bool) ->
    match v binding i with
      | True -> False
      | False -> True ;;

let and =
  fun (b1 : bool) ->
    fun (b2 : bool) ->
      match b1 binding b1 with
      | True -> b2
      | False -> False
;;

let or =
  fun (b1 : bool) ->
    fun (b2 : bool) ->
      match b1 binding b1 with
      | True -> True
      | False -> b2
;;

struct
type t = list

let lookup =
  fix (lookup : t -> nat -> bool) =
    fun (l : t) ->
      fun (x : nat) ->
        match l binding l with
        | Nil -> False
        | Cons -> match compare (l.0) x binding c with
                  | EQ -> True
                  | LT -> lookup (l.1) x
                  | GT -> False
;;

let empty = Nil;;

let insert =
  fix (insert : t -> nat -> t) =
    fun (l : t) ->
      fun (x : nat) ->
        match l binding lp with
        | Nil -> Cons (x, Nil)
        | Cons ->
          (match compare x (lp.0) binding c with
           | LT -> Cons (x, l)
           | EQ -> l
           | GT -> Cons (lp.0, (insert lp.1 x)))
;;

let delete =
  fix (delete : t -> nat -> t) =
    fun (l : t) ->
      fun (x : nat) ->
        match l binding lp with
        | Nil -> Nil
        | Cons ->
          (match compare x (lp.0) binding c with
           | LT -> l
           | EQ -> lp.1
           | GT -> Cons (lp.0, (delete lp.1 x)))
;;

end
:
sig
  type t

  val lookup : t -> nat -> bool
  val empty : t
  val insert : t -> nat -> t
  val delete : t -> nat -> t
end
maintains
forall (s : t). forall (i : nat). not (lookup (delete s i) i)
"

let problem =
  Parser.unprocessed_problem
    Lexer.token (Lexing.from_string problem_string)

let full_spec =
  ProcessFile.process_full_problem
    problem

(*let _ =
  let ans =
    Verifiers.QuickCheckVerifier.implication_counter_example
      ~problem:full_spec
      ~pre:(Expr.mk_func ("x",Type.Var "t")
              (Expr.mk_app
                 (Expr.mk_app
                    (Expr.mk_var "and")
                    ((Value.to_exp (Verifiers.QuickCheckVerifier.true_val))))
                 (Value.to_exp (Verifiers.QuickCheckVerifier.true_val))
              )
              )
      ~eval:(Expr.mk_func ("x",Type.Var "t") (Expr.mk_var "x"))
      ~post:full_spec.post
  in
  begin match ans with
    | None -> failwith "Nonegrr"
    | Some anses -> print_endline (string_of_list Value.show anses)
  end*)

module QCMIG = MIG.MIGLearner(Verifiers.QuickCheckVerifier)

let _ = print_endline @$ QCMIG.learnInvariant ~unprocessed_problem:problem
