type nat =
  | O
  | S of nat

let fst : nat * nat -> nat |>
 { (0, 1) => 0
 ; (2, 3) => 2
 } = ?
