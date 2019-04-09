type nat =
  | O
  | S of nat

let rec sum (n1: nat) (n2: nat) : nat =
  match n1 with
    | O -> n2
    | S n3 -> S (sum n3 n2)
;;

let record_sum : {a:nat; b:nat; c:nat} -> nat |>
  { {a=1;b=2;c=0} => 3
  | {a=1;b=5;c=3} => 9
  | {a=1;b=0;c=1} => 2
  | {a=3;b=0;c=1} => 4  } = ?
