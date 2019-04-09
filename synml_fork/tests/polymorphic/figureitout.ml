type ?a listp =
  | Nilp
  | Consp of (?a * ?a listp)


let rec fold (l:?a listp) (f:?a listp -> ?a -> ?a listp) (acc:?a listp) : ?a
listp =
  match l with
  | Nilp -> acc
  | Consp (hd,tl) -> fold tl f (f acc hd)
;;


let figureitout : ((?a listp) listp) listp -> ?a listp |>
{ Nilp => Nilp } = ?
  (*(?a,1 => ?a,2 | ?a,2 => ?a,3) => ({?a} Consp (?a,1, {?a} Nilp) => {?a} Consp
(?a,2, {?a} Nilp)| {?a} Nilp => {?a} Nilp) } = ?*)
