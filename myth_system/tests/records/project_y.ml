type nat =
  | O
  | S of nat

let getY : {x:nat; y:nat} -> nat |>
  { {x = 0; y = 1 } => 1
  | {x = 1; y = 0 } => 0 } = ?

