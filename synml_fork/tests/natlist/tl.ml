type nat =
  | O
  | S of nat

type natlist =
  | Nil
  | Cons of nat * natlist

let tl : natlist -> natlist |>
  { [] => []
  | [0] => []
  | [0; 0] => [0] } = ?
