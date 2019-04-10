type nat =
  | O
  | S of nat

let getXsnd : {x:(nat * nat)} -> nat |>
  { {x = (0,1)} => 1
  | {x = (1,0)} => 0 } = ?
