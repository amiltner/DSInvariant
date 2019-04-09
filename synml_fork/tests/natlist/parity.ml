(* This is really a boollist example, not a natlist example *)

type nat =
  | O
  | S of nat

type bool =
  | True
  | False

type list =
  | Nil
  | Cons of bool * list

(* 
let xor : bool -> bool -> bool =
  fun (b1:bool) -> fun (b2:bool) ->
  match b1 with
  | True -> 
      ( match b2 with
        | True -> False
        | False -> True )
  | False -> b2
;;
*)

let even_parity : list -> bool |>
    { [] => True
    | [ False ] => True
    | [ True  ] => False
    | [ False ; False ] => True
    | [ False ; True ] => False
    | [ True  ; False ] => False
    | [ True  ; True ] => True
    } = ?
