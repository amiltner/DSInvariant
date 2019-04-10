type nat =
  | O
  | S of nat

let rec sum (n1: nat) (n2: nat) : nat =
  match n1 with
    | O -> n2
    | S n3 -> S (sum n3 n2)
;;

let rec mult2 (n: nat) : nat =
  match n with
    | O -> O
    | S n2 -> S (S (mult2 n2))
;;

let record_sum (r: {a:nat; b:nat; c:nat}) : nat =
  sum (sum (mult2 r.a) (mult2 r.b)) (mult2 r.c)
;;

let record_sum2 : {a:nat; b:nat; c:nat} -> nat -> nat |>
  { {a=1; b=2; c=1} => ( 0 => 8
                       | 1 => 9 )
  | {a=2; b=1; c=1} => ( 0 => 8
                       | 1 => 9 )
  | {a=1; b=1; c=1} => ( 3 => 9
                       | 0 => 6 )
} = ?
