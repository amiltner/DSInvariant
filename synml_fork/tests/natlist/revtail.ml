(* TODO: combinatorial problem, same as the other revs... *)

(*
let rec rev_tail l1 l2 =
  match l1 with
  | []     -> l2
  | n1::l3 -> rev_tail l3 (n1::l2)
*)

type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

let revtail : list -> list -> list |>
  { [] => ( [] => []
          | [0] => [0]
          | [1] => [1]
          | [0;0] => [0;0]
          | [0;1] => [0;1]
          | [1;0] => [1;0]
          | [1;1] => [1;1]
          | [1;0;1] => [1;0;1]
          )
  | [0] => ( [] => [0]
           )
  | [1] => ( [] => [1]
           | [0] => [1;0]
           | [1] => [1;1]
           | [0;1] => [1;0;1]
           )
  | [0;1] => ( [] => [1;0]
             )
  } = ?
