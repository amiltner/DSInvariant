type nat =
   | O
   | S of nat

type nlist =
   | Nil
   | Cons of nat * nlist

type llist =
   | LNil
   | LCons of nlist * llist

let rec nappend (l1:nlist) (l2:nlist) : nlist =
   match l1 with
   | Nil -> l2
   | Cons (x, l1) -> Cons (x, nappend l1 l2)
;;

let rec lappend (l1:llist) (l2:llist) : llist =
   match l1 with
   | LNil -> l2
   | LCons (x, l1) -> LCons (x, lappend l1 l2)
;;


let rot_helper : nlist -> nlist -> llist |>
   { [] => [1;2;3] => LNil
   | [3]  => [1;2] => LCons( [3;1;2], LNil)
   | [2;3]  => [1] => LCons( [2;3;1], LCons([3;1;2], LNil))
   | [1;2;3] => [] => LCons( [1;2;3], LCons( [2;3;1], LCons([3;1;2], LNil)))
   | [] => [2;1;0;3] => LNil
   | [3]  => [2;1;0] => LCons([3;2;1;0], LNil)
   | [0;3]  => [2;1] => LCons([0;3;2;1], LCons([3;2;1;0], LNil))
   | [1;0;3]  => [2] => LCons( [1;0;3;2], LCons([0;3;2;1], LCons([3;2;1;0], LNil)))
   | [2;1;0;3] => [] => LCons( [2;1;0;3], LCons( [1;0;3;2], LCons([0;3;2;1], LCons([3;2;1;0], LNil))))
   } = ?


(*
let rec rot_helper l tl =
   begin match l with
   | [] -> []
   | x::xs -> (l @ tl) :: (rot_helper xs (tl @ [x]))
   end


*)
