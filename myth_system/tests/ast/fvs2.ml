type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

type exp =
  | Unit
  | Var of nat
  | Lam of nat * exp
  | App of exp * exp

let rec append (l1:list) (l2:list) : list =
  match l1 with
  | Nil -> l2
  | Cons (hd, tl) -> Cons (hd, append tl l2)
;;

let fvs : exp -> list |>
  { Unit => []
  | Var (0) => [0]
  | Var (1) => [1]
  | Lam (0, Unit) => []
  | Lam (0, Var (1)) => [1]
  | App (Unit, Unit) => []
  | App (Var (0), Unit) => [0]
  | App (Unit, Var (1)) => [1]
  | App (Var (0), Var (1)) => [0; 1]
  } = ?
