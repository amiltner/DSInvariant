type bool =
  | True
  | False

let xor : bool -> bool -> bool |>
  { True => True => False
  ; True => False => True
  ; False => True => True
  ; False => False => False } = ?
