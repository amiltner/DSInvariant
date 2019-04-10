type nat =
  | O
  | S of nat

let construct_record : nat -> nat -> {x:nat; y:nat}  |>
  {  0 => 1 => {x = 0; y = 1 }
  |  1 => 0 => {x = 1; y = 0 } } = ?

