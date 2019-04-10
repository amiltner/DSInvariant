type nat =
  | O
  | S of nat

let snd : nat * nat -> nat |>
 { (0, 1) => 1
 ; (2, 3) => 3
 } = ?
