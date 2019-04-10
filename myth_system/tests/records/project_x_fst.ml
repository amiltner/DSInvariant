type nat =
  | O
  | S of nat

let getXfst : {x:(nat * nat)} -> nat |>
  { {x = (0,1)} => 0
  | {x = (1,0)} => 1 } = ?
