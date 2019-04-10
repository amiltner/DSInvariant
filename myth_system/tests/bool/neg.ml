type bool =
  | True
  | False

let neg : bool -> bool |>
  { True => False
  ; False => True } = ?
