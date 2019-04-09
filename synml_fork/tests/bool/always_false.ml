type bool =
  | True
  | False

let always_false : bool -> bool |>
  { True => False
  ; False => False } = ?
