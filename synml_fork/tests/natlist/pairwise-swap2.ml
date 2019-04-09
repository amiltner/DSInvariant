type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

type cmp =
  | LT
  | EQ
  | GT

type bool =
  | True
  | False

let rec odd (l:list) : bool =
  match l with
  | Nil -> False
  | Cons (hd, tl) ->
    ( match tl with
    | Nil -> True
    | Cons (h, t) -> odd t )
;;

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

let rec div2 (n:nat) : nat =
  match n with
  | O -> O
  | S n1 -> match n1 with
    | O -> O
    | S n2 -> S (div2 n2)
;;                  

let rec compare (n1 : nat) (n2 :nat) : cmp =
  match n1 with
  | O -> ( match n2 with 
           | O -> EQ
           | S m -> LT
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


let pairwise_swap : list -> list |>
{
  [] => []
| [0] => []
| [1] => []
| [2] => []
| [2;2] => [2;2]
| [0;1] => [1;0]
| [1;0] => [0;1]
| [1;2] => [2;1]           
| [2;1] => [1;2]
| [0;2] => [2;0]
| [0;1;0] => []
| [1;0;1] => []           
| [2;0;2] => []
| [1;2;1] => []
| [2;1;2] => []
| [0;1;0;1] => [1;0;1;0]
| [1;0;1;0] => [0;1;0;1]
| [1;2;1;2] => [2;1;2;1]
| [0;1;2;1] => [1;0;1;2]
| [0;2;0;2] => [2;0;2;0]
} = ?
