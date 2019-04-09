type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

let length : list -> nat |>
  { [] => 0
  | [0] => 1
  | [0;0] => 2 } = ?
