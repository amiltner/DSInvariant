type nat =
  | O
  | S of nat

let getfstY : ({x:nat; y:nat} * nat) -> nat |>
  { ({x = 0; y = 1}, 2) => 1
  | ({x = 2; y = 1}, 0) => 1 } = ?
