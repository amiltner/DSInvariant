open Base
open LoopInvGen
open Verifiers

let _ = z3_verifier
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

open SyGuS_Set

let insert_func =
  {
    args = [("x",Type.INT);("y",Type.INT);("z",Type.INT);("x!",Type.INT);("y!",Type.INT);];
    name = "insert";
    expr = "(and (= x! (ite (<= z x) z x)) (= y! (ite (<= z x) y z)))";
    return = Type.BOOL;
  }

let delete_func =
  {
    args = [("x",Type.INT);("y",Type.INT);("z",Type.INT);("x!",Type.INT);("y!",Type.INT);];
    name = "delete";
    expr = "(and (= x! (ite (< z x) x (ite (= z x) y x))) (= y! (ite (< z x) y (ite (= z x) 2147483647 (ite (= z y) 2147483647 y)))))";
    return = Type.BOOL;
  }

let lookup_func =
  {
    args = [("x",Type.INT);("y",Type.INT);("z",Type.INT)];
    name = "lookup";
    expr = "(or (= z x) (= z y))";
    return = Type.BOOL;
  }

let post_func =
  {
    args = [("x",Type.INT);("y",Type.INT)];
    name = "post";
    expr = "(forall ((z Int) (x! Int) (y! Int)) (and (delete x y z x! y!) (not (lookup x! y! z))))";
    return = Type.BOOL;
  }

(*let v = empty
let v = register_func v insert_func
let v = register_func v delete_func
let v = register_func v lookup_func
  let v = register_func v post_func*)

let sygus_call =
  {
    insert_func = insert_func;
    delete_func = delete_func;
    lookup_func = lookup_func;
    post_func = post_func;
    constants = [];
    synth_variables = [];
  }

open SIG

let _ =
  learnSetInvariant
    ~states:[]
    sygus_call

let _ = Z3Verifier.register_func Z3Verifier.empty
    {
      args = [("x",Type.INT);("y",Type.INT);("z",Type.INT);("x!",Type.INT);("y!",Type.INT);];
      name = "delete";
      expr = "(and (= x! (ite (< z x) x (ite (= z x) y x))) (= y! (ite (< z x) y (ite (= z x) 2147483647 (ite (= z y) 2147483647 y)))))";
      return = Type.BOOL;
    }
