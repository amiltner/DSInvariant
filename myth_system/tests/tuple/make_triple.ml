type nat =
  | O
  | S of nat

let make_triple : nat -> nat -> nat -> nat * nat * nat |>
 { 0 => 1 => 2 => (0, 1, 2)
 | 3 => 4 => 5 => (3, 4, 5)
 } =
?
