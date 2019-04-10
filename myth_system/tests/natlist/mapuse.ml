type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

let rec map (l:list) (f : nat -> nat) : list =
     match l with
       | Nil -> Nil
       | Cons (hd, tl) -> Cons (f hd, map tl f)
;;

let map_use : list -> list |>
  { [] => []
  | [1;2] => [2;3]
  | [0;0] => [1;1]
  | [3;4;5] => [4;5;6]
  } = ?
