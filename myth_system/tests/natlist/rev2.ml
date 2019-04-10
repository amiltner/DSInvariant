type nat =
  | O
  | S of nat

type list =
  | Nil
  | Cons of nat * list

(* For some reason, commenting out 'apply' causes an error. *)
(*
let apply : ((list -> nat -> list) -> list -> list) -> (list -> nat -> list) -> list -> list =
  fun (body : ((list -> nat -> list) -> list -> list)) ->
  fun (f : list -> nat -> list) ->
  fun (l : list) ->
  body f l
;;
*)

let snoc : list -> nat -> list =
  let rec f (l:list) : nat -> list =
    fun (n:nat) ->
      match l with
      | Nil -> Cons (n, Nil)
      | Cons (hd, tl) -> Cons (hd, f tl n)
  in
    f
;;


let rev : list -> list |>
  { [] => []
  | [0] => [0]
  | [1] => [1]
  | [2] => [2]
  | [0;0] => [0;0]
  | [0;1] => [1;0]
  | [2;0] => [0;2]
  | [2;1] => [1;2]
  | [1;0] => [0;1]
  | [0;0;1] => [1;0;0]
  | [0;1;0] => [0;1;0]
  | [0;1;2] => [2;1;0]
  | [0;2;1] => [1;2;0]
  | [1;0;0] => [0;0;1]
  | [0;0;2;1] => [1;2;0;0]
  | [0;1;0;0] => [0;0;1;0]
  } = ?

