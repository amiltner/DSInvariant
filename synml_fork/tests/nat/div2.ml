type nat =
  | O
  | S of nat

let div2 : nat -> nat |>
  { 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2 } = ?
