type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

let interleave : list -> list -> list |>
{ [] => ( [] => []
        | [1] => [1]
        )
|[2] => ( [] => [2]
        | [1] => [2;1]
        | [3;1] => [2;3;1]
        )
|[1;2] => ( [] => [1;2]
         | [1] => [1;1;2]       
         )
  } = ?
