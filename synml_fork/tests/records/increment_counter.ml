type nat =
  | O
  | S of nat

let increment_counter : {counter:nat; other:nat} -> {counter:nat; other:nat} |>
  { {counter = 0; other = 1 } => {counter = 1; other = 1 }
  | {counter = 5; other = 2 } => {counter = 6; other = 2 } } = ?
