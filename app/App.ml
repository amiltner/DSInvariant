open Base
open LoopInvGen


let empty = (Int.max_value, Int.max_value)

let insert z (x,y) =
  if z <= x then
    (z,y)
  else
    (x,z)

let contains z (x,y) =
  z = x || z = y

let delete z (x,y) =
  if z < x then
    (x,y)
  else if z = x then
    (y,Int.max_value)
  else if z = y then
    (x,Int.max_value)
  else
    (x,y)


(* a job for inferring an equivalence relation between two representations of a\
 counter data structure (adapted from Dave Walker's course notes) *)
let equiv_job = Job.create
    ~f:(fun [@warning "-8"] [ Value.Int x; Value.Int y; Value.Int z] ->
        Value.Bool (contains z (delete z (x,y))))
    ~args:([ ("Q = contains x (delete x s) = false
Now, with Set implementation:
LOOP 1:
151: I = VPreGen([], Q, {}) = false
        8: P = PIE({},{}) = true
        9: t = ANDERSVERIFY(true,[],Q) = Some (2,(4,2))
        8: P = PIE({},{(2,(4,2))}) = true
        9: t = ANDERSVERIFY(false,[],Q) = None
152: e = PushBoundary(S,G,s = insert y s,I) = None
155: continues
163: e = PushBoundary(S,G,s = insert y s,I) = None
166: continues
174: cex = Valid(I(S.empty)) = (S.empty)

LOOP 2:
151: I = VPreGen([], Q, {(0,S.empty)}) = (s == S.empty)
        8: P = PIE({(0,S.empty)},{}) = true
        9: t = ANDERSVERIFY(true,[],Q) = Some (2,(4,2))
        8: P = PIE({S.empty},{(2,(4,2))}) = (x <= 0)
        9: t = ANDERSVERIFY(x <= 0,[],Q) = Some (-2,(4,-2))
        8: P = PIE({S.empty},{(2,(4,2)),(-2,(4,-2))}) = (s == S.empty)
               NB: (actually it was the correct s.1 <= s.2, but for the sake of
                   interest)
        9: t = ANDERSVERIFY(s == S.empty,[],Q) = None
152: e = PushBoundary(S,G,s = insert y s,s == S.empty) = Some (-1,(0,Int.max))
        35: cex = ANDERSVERIFY(true, [s = empty; s = insert y s], s == S.empty) ---> (-1,(0,Int.max))

LOOP 3:
151: I = VPreGen([], Q, {(0,S.empty) ; (-1,(0,Int.max))}) = (s.1 <= s.2)
        8: P = PIE({(0,S.empty) ; (-1,(0,Int.max))},{}) = true
        9: t = ANDERSVERIFY(true,[],Q) = Some (2,(4,2))
        8: P = PIE({(0,S.empty) ; (-1,(0,Int.max))},{(2,(4,2))}) = (x <= 0)
        9: t = ANDERSVERIFY(x <= 0,[],Q) = Some (-2,(4,-2))
        8: P = PIE({(0,S.empty) ; (-1,(0,Int.max))},{(2,(4,2)),(-2,(4,-2))}) = s.1 <= s.2
        9: t = ANDERSVERIFY(s == S.empty,[],Q) = None
rest goes through simply


x", Type.INT); ("y", Type.INT); ("z", Type.INT) ])
    ~post:(fun inp _ ->
        match inp with
        | [ Value.Int x; Value.Int y; Value.Int z ] ->
          Stdio.print_endline (Int.to_string x);
          Stdio.print_endline (Int.to_string y);
          Stdio.print_endline (Int.to_string z);
          not (contains z (delete z (x,y)))
        | _ -> false)
    ~features:[]
    (List.map [(0,empty); (-1,(0,Int.max_value))] ~f:(fun (x,(y,z)) -> [Value.Int y ; Value.Int z; Value.Int x]))

let () =
  Stdio.print_endline (
      "The precondition is: "
    ^ PIE.cnf_opt_to_desc (PIE.learnPreCond equiv_job)
  )
