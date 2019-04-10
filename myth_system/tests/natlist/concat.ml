type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

type llist =
  | LNil
  | LCons of list * llist

(*
let append : list -> list -> list =
  let rec g (xs1:list) (xs2:list) : list =
    match xs1 with
    | Nil -> xs2
    | Cons (x, xs1p) -> Cons (x, g xs1p xs2)
  in
    g
;;
*)

let rec append (l1:list) (l2:list) : list =
  match l1 with
  | Nil -> l2
  | Cons (hd, tl) -> Cons (hd, append tl l2)
;;

let concat : llist -> list |>
  { LNil => []
  | LCons ([], LNil) => []
  | LCons ([0], LNil) => [0]
  | LCons ([0], LCons([0], LNil)) => [0;0]
  | LCons ([1], LNil) => [1]
  | LCons ([1], LCons([1], LNil)) => [1;1]
  } = ?
