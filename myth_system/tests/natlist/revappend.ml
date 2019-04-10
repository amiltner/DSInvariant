(* TODO: same as rev.ml --- need to enumerate all tests up to length 3, most likely... *)

type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

let rec append (l1:list) (l2:list) : list =
  match l1 with
  | Nil -> l2
  | Cons (hd, tl) -> Cons (hd, append tl l2)
;;

let revappend : list -> list |>
  { [] => []
  | [0] => [0]
  | [1] => [1]
  | [0;0] => [0;0]
  | [0;1] => [1;0]
  | [0;0;1] => [1;0;0]
  } = ?
