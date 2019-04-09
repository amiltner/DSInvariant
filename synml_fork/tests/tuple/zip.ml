type bool =
  | T
  | F

type list =
  | Nil
  | Cons of bool * list

type pairlist =
  | PNil
  | PCons of (bool * bool) * pairlist

type pairlist_option =
  | None
  | Some of pairlist

let zip : list -> list -> pairlist_option |>
{
  Nil =>       ( Nil    => Some (PNil)
               | [T]    => None
               | [F]    => None
               | [T; T] => None
               | [T; F] => None
               | [F; T] => None
               | [F; F] => None)
| [T] =>       ( Nil    => None
               | [T]    => Some (PCons((T, T), PNil))
               | [F]    => Some (PCons((T, F), PNil))
               | [T; T] => None
               | [T; F] => None
               | [F; T] => None
               | [F; F] => None)
| [F] =>       ( Nil    => None
               | [T]    => Some (PCons((F, T), PNil))
               | [F]    => Some (PCons((F, F), PNil))
               | [T; T] => None
               | [T; F] => None
               | [F; T] => None
               | [F; F] => None)
| [T; T] =>    ( Nil    => None
               | [T]    => None
               | [F]    => None
               | [T; T] => Some (PCons((T, T), PCons((T, T), PNil)))
               | [T; F] => Some (PCons((T, T), PCons((T, F), PNil)))
               | [F; T] => Some (PCons((T, F), PCons((T, T), PNil)))
               | [F; F] => Some (PCons((T, F), PCons((T, F), PNil))))
| [F; F] =>    ( Nil    => None
               | [T]    => None
               | [F]    => None
               | [T; T] => Some (PCons((F, T), PCons((F, T), PNil)))
               | [T; F] => Some (PCons((F, T), PCons((F, F), PNil)))
               | [F; T] => Some (PCons((F, F), PCons((F, T), PNil)))
               | [F; F] => Some (PCons((F, F), PCons((F, F), PNil))))
| [T; F] =>    ( Nil    => None
               | [T]    => None
               | [F]    => None
               | [T; T] => Some (PCons((T, T), PCons((F, T), PNil)))
               | [T; F] => Some (PCons((T, T), PCons((F, F), PNil)))
               | [F; T] => Some (PCons((T, F), PCons((F, T), PNil)))
               | [F; F] => Some (PCons((T, F), PCons((F, F), PNil))))
| [F; T] =>    ( Nil    => None
               | [T]    => None
               | [F]    => None
               | [T; T] => Some (PCons((F, T), PCons((T, T), PNil)))
               | [T; F] => Some (PCons((F, T), PCons((T, F), PNil)))
               | [F; T] => Some (PCons((F, F), PCons((T, T), PNil)))
               | [F; F] => Some (PCons((F, F), PCons((T, F), PNil))))

} = ?
