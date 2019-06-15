let prelude_string = "
(* PRELUDE *)

type bool =
  | False
  | True

let not =
  fun (v : bool) ->
    match v binding i with
    | False -> True
    | True -> False
;;

let and =
  fun (b1 : bool) ->
    fun (b2 : bool) ->
      match b1 binding b1 with
      | False -> False
      | True -> b2
;;

let or =
  fun (b1 : bool) ->
    fun (b2 : bool) ->
      match b1 binding b1 with
      | False -> b2
      | True -> True
;;

let implies =
  fun (b1 : bool) ->
    fun (b2 : bool) ->
      (or (not b1) b2)
;;

type cmp =
  | LT
  | EQ
  | GT

let is_eq =
  fun (c:cmp) ->
    match c binding c with
    | LT -> False
    | EQ -> True
    | GT -> False
;;

type nat = mu nat .
  | O
  | S of nat

let cmp_nat =
  fix (cmp_nat : nat -> nat -> cmp) =
    fun (x1 : nat) ->
      fun (x2 : nat) ->
        match x1 binding x1 with
        | O -> (match x2 binding x2 with
                | O -> EQ
                | S -> LT)
        | S -> (match x2 binding x2 with
                | O -> GT
                | S -> cmp_nat x1 x2)
;;

let add =
  fix (add : nat -> nat -> nat) =
    fun (x1 : nat) ->
      fun (x2 : nat) ->
        match x1 binding x1 with
        | O -> x2
        | S -> add x1 (S x2)
;;

(* END_PRELUDE *)

"
