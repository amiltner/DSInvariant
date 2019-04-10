type nat =
  | O
  | S of nat

let make_pair : nat -> nat -> nat * nat |>
 { 0 => 1 => (0, 1)
 ; 2 => 3 => (2, 3)
 } = ?
