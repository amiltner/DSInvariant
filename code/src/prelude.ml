let prelude_string =
  "
(* PRELUDE *)

type bool =
  | True
  | False

let not =
  fun (v : bool) ->
    match v binding i with
    | True -> False
    | False -> True
;;

let and =
  fun (b1 : bool) ->
    fun (b2 : bool) ->
      match b1 binding b1 with
      | True -> b2
      | False -> False
;;

let or =
  fun (b1 : bool) ->
    fun (b2 : bool) ->
      match b1 binding b1 with
      | True -> True
      | False -> b2
;;

let implies =
  fun (b1 : bool) ->
    fun (b2 : bool) ->
      (or (not b1) b2)
;;

(* END_PRELUDE *)

"
