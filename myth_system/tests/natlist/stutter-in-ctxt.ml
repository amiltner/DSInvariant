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

let rec sum (n1:nat) (n2:nat) : nat =
  match n1 with
  | O -> n2
  | S n1 -> S (sum n1 n2)
;;

let rec minus (n1:nat) (n2:nat) : nat =
  match n1 with
  | O -> O
  | S n1 ->
    match n2 with
    | O -> S (n1)
    | S n2 -> minus n1 n2
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

let stutter : list -> list |>
  { [] => []
  | [0] => [0;0]
  | [1;0] => [1;1;0;0]
  } = ?
