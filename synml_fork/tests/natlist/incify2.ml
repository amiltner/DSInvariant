type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

let rec map (l:list) (f:nat -> nat) : list =
  match l with
  | Nil -> Nil
  | Cons (hd, tl) -> Cons (f hd, map tl f)
;;

let incify : list -> list |>
  { [] => []
  | [0] => [1]
  | [1] => [2]
  } = ?
