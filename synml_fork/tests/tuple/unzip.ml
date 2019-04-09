type bool =
  | T
  | F

type list =
  | Nil
  | Cons of bool * list

type pairlist =
  | PNil
  | PCons of (bool * bool) * pairlist

let unzip : pairlist -> list * list |>
{ PNil                 => (Nil, Nil)
| PCons ((T, T), PNil) => ([T], [T])
| PCons ((T, F), PNil) => ([T], [F])
| PCons ((F, T), PNil) => ([F], [T])
| PCons ((F, F), PNil) => ([F], [F])
| PCons ((F, T), PCons ((T, T), PNil)) => ([F; T], [T; T])
| PCons ((F, F), PCons ((F, T), PNil)) => ([F; F], [F; T])
} = ?
