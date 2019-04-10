type nat =
  | O
  | S of nat

let rec plus (n1:nat) (n2:nat) : nat =
  match n1 with
  | O -> n2
  | S n1 -> S (plus n1 n2)
;;

let antagonistic : nat -> nat |>
{  0 => 3
 | 1 => S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(0))))))))))))))))))
 | 2 => S(S(S(S(S(S(S(S(S(S(S(S(0))))))))))))
 | 3 => 6
 | 4 => S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(0)))))))))))))))))))))))
} = ?
