type bool =
  | True
  | False

type tree =
  | Leaf
  | Node of tree * bool * tree

type nat =
  | O
  | S of nat

let rec sum (n1:nat) (n2:nat) : nat =
  match n1 with
  | O -> n2
  | S n1 -> S (sum n1 n2)
;;

let count_leaves : tree -> nat |>
  { Leaf => O
  | Node (Leaf, True, Leaf) => S (O)
  | Node (Node (Leaf, True, Leaf), True, Leaf) => S (S (O))
  | Node (Leaf, True, Node (Leaf, True, Leaf)) => S (S (O))
  | Node (Node (Leaf, True, Leaf), True, Node (Leaf, True, Leaf)) => S (S (S (O)))
  } = ?
