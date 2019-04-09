type nat =
  | O
  | S of nat

let swap: {x:nat; y:nat} -> {x:nat; y:nat} |>
  { {x=0; y=1} => {x=1; y=0}
  | {x=1; y=0} => {x=0; y=1} } = ?
