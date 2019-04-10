type nat =
  | O
  | S of nat

let make_quadruple : nat -> nat -> nat -> nat -> nat * nat * nat * nat |>
 { 0 => 1 => 2 => 3 => (0, 1, 2, 3)
 | 4 => 5 => 6 => 7 => (4, 5, 6, 7)
 } = ?
