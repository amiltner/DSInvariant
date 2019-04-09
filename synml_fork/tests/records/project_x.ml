type nat =
  | O
  | S of nat

let getX : {x:nat; y:nat} -> nat |>
  { {x = 0; y = 1 } => 0
  | {x = 1; y = 0 } => 1 } = ?
