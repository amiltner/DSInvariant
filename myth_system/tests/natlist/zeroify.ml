type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

(* NOTE: right now, letrec only assumes the first argument is decreasing so
 * the arguments to map are in a funny order.  Really, we need to assume that
 * lecrec'ed defs are all well-founded --- or actually verify this at typechecking *)
let rec map (l:list) (f:nat -> nat) : list =
  match l with
  | Nil -> Nil
  | Cons (hd, tl) -> Cons (f hd, map tl f)
;;

let zeroify : list -> list |>
  { [] => []
  | [1] => [0]
  } = ?
