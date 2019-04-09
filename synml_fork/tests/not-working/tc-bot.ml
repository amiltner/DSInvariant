(* -matches 2 -scrutinee 8 *)

type nat =
| O
| S of nat

type typ =
| Bot
| TUnit
| Arr of typ * typ

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
  | Bot ->
    (match t2 with
     | Bot -> True
     | TUnit -> False
     | Arr (t21, t22) -> False)
  | TUnit ->
    (match t2 with
     | Bot -> False
     | TUnit -> True
     | Arr (t21, t22) -> False)
  | Arr (t11, t12) ->
    (match t2 with
     | Bot -> False
     | TUnit -> False
     | Arr (t21, t22) -> band (ty_eq t11 t21) (ty_eq t12 t22))
;;

let rec lookup (g:ctx) (x:nat) : typ =
  match g with
  | Empty -> Bot
  | Cons (y, t, g) ->
    (match nat_eq x y with
    | True -> t
    | False -> lookup g x)
;;

let tc : exp -> ctx -> typ |>
{
  Unit => ( Empty => TUnit
            | Cons (0, TUnit, Empty) => TUnit
            | Cons (0, Arr (TUnit, TUnit), Empty) => TUnit
            | Cons (0, Arr (TUnit, Arr(TUnit, TUnit)), Empty) => TUnit
            )
  | Var (0) => ( Empty => Bot
               | Cons (0, TUnit, Empty) => TUnit
               | Cons (0, Arr (TUnit, TUnit), Empty) => Arr (TUnit, TUnit)
               | Cons (0, Arr (TUnit, Arr(TUnit, TUnit)), Empty) => Arr (TUnit, Arr(TUnit, TUnit))
               | Cons (0, Arr (TUnit, Arr(TUnit,TUnit)), Cons (1, TUnit, Empty)) => Arr (TUnit, Arr(TUnit,TUnit))
               )
  | Var (1) => ( Empty => Bot
               | Cons (0, TUnit, Empty) => Bot
               | Cons (1, TUnit, Empty) => TUnit
               | Cons (0, TUnit, Cons (1, TUnit, Empty)) => TUnit
               | Cons (0, Arr (TUnit, Arr(TUnit,TUnit)), Cons (1, TUnit, Empty)) => TUnit         
               )

  | Lam (0, Arr (TUnit, TUnit), Unit) => Empty => Arr (Arr (TUnit, TUnit), TUnit)
  | Lam (0, Arr (TUnit, TUnit), Var (0)) => Empty => Arr (Arr (TUnit, TUnit), Arr (TUnit, TUnit))
  | Lam (0, TUnit, Var (0)) => Empty => Arr (TUnit, TUnit)
  | Lam (0, TUnit, Var (0)) => Cons (1, TUnit, Empty) => Arr (TUnit, TUnit)
  | Lam (0, Bot, Var (0)) => Cons (1, TUnit, Empty) => Arr (Bot, Bot)
  | Lam (0, TUnit, Var (1)) => Empty => Bot
  | Lam (0, Bot, Unit) => Empty => Arr (Bot, TUnit)
  | Lam (1, TUnit, Var (1)) => Empty => Arr (TUnit, TUnit)
  | Lam (0, TUnit, Var (1)) => Cons (1, TUnit, Empty) => Arr (TUnit, TUnit)
  | Lam (0, TUnit, Var (1)) => Cons (1, Bot, Empty) => Arr (TUnit, Bot)      
  | Lam (1, TUnit, Lam (0, TUnit, Var (0))) => Empty => Arr (TUnit, Arr(TUnit, TUnit))
  | Lam (1, Bot, Lam (0, TUnit, Var (1))) => Empty => Arr (Bot, Arr(TUnit, Bot))      
  | Lam (1, TUnit, Lam (0, Bot, Var (0))) => Empty => Arr (TUnit, Arr(Bot, Bot))

  | App (Var (0), Unit) => Empty => Bot

  | App (Unit, Unit) => Empty => Bot

  | App (Var (0), Unit) => Cons (0, Arr (TUnit, TUnit), Empty) => TUnit

  | App (Var (0), Var (0)) => Cons (0, Arr (TUnit, TUnit), Empty) => Bot

  | App (Var (0), Var (1)) => Cons (0, Arr (TUnit, Arr(TUnit,TUnit)), Cons (1, TUnit, Empty)) => Arr(TUnit, TUnit)

  | App (Var (1), Var (0)) => Cons (0, Arr (TUnit, ), Cons (1, TUnit, Empty)) => Arr(TUnit, TUnit)

  | App (Lam (0, TUnit, Var (0)), Unit) => Empty => TUnit

  | App (Lam (0, Bot, Unit), App(Unit, Unit)) => Empty => TUnit

} = ?


(*
Desired Target:

let tc : exp -> ctx -> typ =
  let rec f1 (e1:exp) : ctx -> typ =
    fun (c1:ctx) ->
      match e1 with
        | Unit -> TUnit
        | Var (n1) -> lookup c1 n1
        | Lam (n1, t1, e2) -> (match f1 e2 (Cons (n1, t1, c1)) with
                                 | Bot -> Bot
                                 | TUnit -> Arr(t1, TUnit)
                                 | Arr (t11, t12) -> Arr(t1, Arr(t11, t12))
        | App (e2, e3) -> (match f1 e2 c1 with
                             | Bot -> Bot
                             | TUnit -> Bot
                             | Arr (t11, t12) ->
                             (match eq_typ t11 (f1 e3 c1) with
                              | True -> t12
                              | False -> Bot))
  in             
    f1
;;
*)
