type nat =
  | O
  | S of nat

let getC: {a:nat; b:nat; c:nat; d:nat; e:nat} -> nat |>
  { {a = 0; b = 1; c = 2; d = 3; e = 4} => 2
  | {a = 4; b = 3; c = 2; d = 1; e = 0} => 2 } = ?
