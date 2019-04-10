type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

type tree =
  | Leaf
  | Node of tree * nat * tree


type cmp =
  | LT
  | EQ
  | GT

type bool =
  | True
  | False

let rec andb (n1:bool) (n2:bool) : bool =
  match n1 with
  | True -> n2
  | False -> False
;;

let rec orb (n1:bool) (n2:bool) : bool =
  match n1 with
  | True -> True
  | False -> n2
;;

let rec sum (n1:nat) (n2:nat) : nat =
  match n1 with
  | O -> n2
  | S n1 -> S (sum n1 n2)
;;

(*
let rec minus (n1:nat) (n2:nat) : nat =
  match n1 with
  | O -> O
  | S (n1) ->
    match n2 with
    | O -> S (n1)
    | S (n2) -> minus n1 n2
;;
*)

let rec div2 (n:nat) : nat =
  match n with
  | O -> O
  | S n1 -> match n1 with
    | O -> O
    | S n2 -> S (div2 n2)
;;                  

let rec inc (n:nat) : nat =
  S (n)
;;

let rec compare (n1 : nat) (n2 :nat) : cmp =
  match n1 with
  | O -> ( match n2 with 
           | O -> EQ
           | S _ -> LT
         )
  | S m1 -> 
      ( match n2 with
      | O -> GT
      | S m2 -> (compare m1 m2) )
;;

let rec append (l1:list) (l2:list) : list =
  match l1 with
  | Nil -> l2
  | Cons (hd, tl) -> Cons (hd, append tl l2)
;;


let tree_map : tree -> list |>
{  Leaf => []
| Node (Leaf, 1, Leaf) => [1]                          
| Node (Leaf, 2, Leaf) => [2]
| Node (Node (Leaf, 1, Leaf), 2, Leaf) => [1;2]
| Node (Leaf, 1, Node (Leaf, 2, Leaf)) => [2;1]
| Node (Node (Leaf, 1, Leaf), 0, Node (Leaf, 2, Leaf) ) => [1;2;0]
| Node (Node (Leaf, 2, Leaf), 0, Node (Leaf, 1, Leaf) ) => [2;1;0]
| Node (Node (Node (Leaf, 2, Leaf), 0, Node (Leaf, 1, Leaf) ), 0, Leaf) => [2;1;0;0]
| Node (Leaf, 2, Node (Node (Leaf, 2, Leaf), 0, Node (Leaf, 1, Leaf) )) => [2;1;0;2]
} = ?
