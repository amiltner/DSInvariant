type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

let rec fold (l:list) (f:list -> nat -> list) (acc:list) : list =
  match l with
  | Nil -> acc
  | Cons (hd, tl) -> fold tl f (f acc hd)
;;


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
  | [0;0] => [0;0]
  | [1;0] => [0;1]
  | [0;0;1] => [1;0;0]
  | [1;0;0] => [0;0;1]
  } = ?

