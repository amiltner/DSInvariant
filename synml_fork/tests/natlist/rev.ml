type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

(*
let rec snoc (l:list) (n:nat) : list =
  match l with
  | Nil -> Cons (n, Nil)
  | Cons (x, xs) -> Cons (x, snoc xs n)
;;
*)

let snoc : list -> nat -> list =
  let rec f (l:list) : nat -> list =
    fun (n:nat) ->
      match l with
      | Nil -> Cons (n, Nil)
      | Cons (hd, tl) -> Cons (hd, f tl n)
  in
    f
;;

let rev : list -> list |>
  { [] => []
  | [0] => [0]
  | [1] => [1]
  | [0;1] => [1;0]
  | [0;0;1] => [1;0;0]
  } = ?
