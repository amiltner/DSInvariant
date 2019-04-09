type nat =
  | O
  | S of nat

type c =
  | B of {x:nat}
  | R of c

let extract : c -> nat |>
  { B ({x = 0}) => 0
  | B ({x = 1}) => 1
  | R (B ({x = 0})) => 0
  | R (B ({x = 1})) => 1 } = ?
