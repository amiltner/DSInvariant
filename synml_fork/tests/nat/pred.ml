type nat =
  | O
  | S of nat

let pred : nat -> nat |>
  { O => O
  ; S (O) => O
  ; S (S (O)) => S (O) } = ?
