type bool =
  | True
  | False

let impl : bool -> bool -> bool |>
  { True => True => True
  ; True => False => False
  ; False => True => True
  ; False => False => True } = ?
