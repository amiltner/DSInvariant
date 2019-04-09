type bool =
  | True
  | False

let always_true : bool -> bool |>
  { True => True
  ; False => True } = ?
