(* -matches 2 -scrutinee 8 *)

type nat =
| O
| S of nat

type typ =
| TUnit
| Arr of typ * typ

type typopt =
| None
| Some of typ

type ctx =
| Empty
| Cons of nat * typ * ctx

type exp =
| Unit
| Var of nat
| Lam of nat * typ * exp
| App of exp * exp

type bool =
| True
| False

let rec nat_eq (x1:nat) (x2:nat) : bool =
  match x1 with
  | O ->
    (match x2 with
    | O -> True
    | S (x2) -> False)
  | S (x1) ->
    (match x2 with
    | O -> False
    | S (x2) -> nat_eq x1 x2)
;;

let band (b1:bool) (b2:bool) : bool =
  match b1 with
  | True -> b2
  | False -> False
;;

let rec ty_eq (t1:typ) (t2:typ) : bool =
  match t1 with
  | TUnit ->
    (match t2 with
    | TUnit -> True
    | Arr (t21, t22) -> False)
  | Arr (t11, t12) ->
    (match t2 with
    | TUnit -> False
    | Arr (t21, t22) -> band (ty_eq t11 t21) (ty_eq t12 t22))
;;

let rec lookup (g:ctx) (x:nat) : typopt =
  match g with
  | Empty -> None
  | Cons (y, t, g) ->
    (match nat_eq x y with
    | True -> Some (t)
    | False -> lookup g x)
;;

let tc : exp -> ctx -> typopt |>
  { Unit => ( Empty => Some (TUnit)
            | Cons (0, TUnit, Empty) => Some (TUnit)
            | Cons (0, Arr (TUnit, TUnit), Empty) => Some (TUnit)
            | Cons (0, Arr (TUnit, Arr(TUnit, TUnit)), Empty) => Some (TUnit)
            )
  | Var (0) => ( Empty => None
               | Cons (0, TUnit, Empty) => Some (TUnit)
               | Cons (0, Arr (TUnit, TUnit), Empty) => Some (Arr (TUnit, TUnit))
               | Cons (0, Arr (TUnit, Arr(TUnit, TUnit)), Empty) => Some (Arr (TUnit, Arr(TUnit, TUnit)))
               )
  | Var (1) => ( Empty => None
               | Cons (0, TUnit, Empty) => None
               | Cons (1, TUnit, Empty) => Some (TUnit)
               | Cons (0, TUnit, Cons (1, TUnit, Empty)) => Some (TUnit)
               )

  | Lam (0, Arr (TUnit, TUnit), Unit) => Empty => Some (Arr (Arr (TUnit, TUnit), TUnit))
  | Lam (0, Arr (TUnit, TUnit), Var (0)) => Empty => Some (Arr (Arr (TUnit, TUnit), Arr (TUnit, TUnit)))
  | Lam (0, TUnit, Var (0)) => Empty => Some (Arr (TUnit, TUnit))
  | Lam (0, TUnit, Var (1)) => Empty => None
  | Lam (1, TUnit, Var (1)) => Empty => Some (Arr (TUnit, TUnit))
  | Lam (0, TUnit, Var (1)) => Cons (1, TUnit, Empty) => Some (Arr (TUnit, TUnit))
  | App (Var (0), Unit) => Cons (0, Arr (TUnit, TUnit), Empty) => Some (TUnit) 
  | App (Var (0), Var (0)) => Cons (0, Arr (TUnit, TUnit), Empty) => None
  | App (Unit, Unit) => Cons (0, Arr (TUnit, TUnit), Empty) => None
  | App (Var (0), Unit) => Cons (0, Arr (TUnit, Arr(TUnit, TUnit)), Empty) => Some (Arr(TUnit, TUnit))
  } = ?


(*
Desired Target:

let tc : exp -> ctx -> typopt =
  let rec f1 (e1:exp) : ctx -> typopt =
    fun (c1:ctx) ->
      match e1 with
        | Unit -> Some (TUnit)
        | Var (n1) -> lookup c1 n1
        | Lam (n1, t1, e2) -> (match f1 e2 (Cons (n1, t1, c1)) with
                                 | None -> None
                                 | Some (t2) -> Some (Arr (t1, t2)))
        | App (e2, e3) -> (match f1 e2 c1 with
                             | None -> None
                             | Some (t1) -> 
                               (match t1 with
                                | TUnit -> None
                                | Arr(t11, t12) ->
                                  (match f1 e3 c1 with
                                   | None -> None
                                   | Some (t2) ->
                                     (match ty_eq t11 t2 with
                                     | True -> Some ( t12 )
                                     | False -> None ))))
  in             
    f1
;;
*)
