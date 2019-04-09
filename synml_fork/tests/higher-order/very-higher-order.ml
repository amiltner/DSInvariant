type nat =
   | O
   | S of nat


let g (f : nat -> nat) : nat =
  f 0
;;

let h (f : nat -> nat) : nat =
  f (f 0 )
;;

let p (f : nat -> nat) : nat =
  f ( f ( f ( f 0 ) ) )
;;

let succ (x:nat) : nat =
  S ( x )
;;

let goal : ( (nat -> nat) -> nat ) -> nat |>
   {
     g => 1
   | h => 2
   | ( (1 => 4) => 4 ) => 4 
   } = ?

