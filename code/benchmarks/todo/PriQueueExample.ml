https://softwarefoundations.cis.upenn.edu/vfa-current/Priqueue.html
https://softwarefoundations.cis.upenn.edu/vfa-current/Binom.html


Module Type PRIQUEUE.
  Parameter priqueue: Type.
  Definition key := nat.
  Parameter empty: priqueue.
  Parameter insert: key → priqueue → priqueue.
  Parameter delete_max: priqueue → option (key * priqueue).
  Parameter merge: priqueue → priqueue → priqueue.
  Parameter priq: priqueue → Prop.
  Parameter Abs: priqueue → list key → Prop.
  Axiom can_relate: ∀ p, priq p → ∃ al, Abs p al.
  Axiom abs_perm: ∀ p al bl, 
   priq p → Abs p al → Abs p bl → Permutation al bl.
  Axiom empty_priq: priq empty.
  Axiom empty_relate: Abs empty nil.
  Axiom insert_priq: ∀ k p, priq p → priq (insert k p).
  Axiom insert_relate:
        ∀ p al k, priq p → Abs p al → Abs (insert k p) (k::al).
  Axiom delete_max_None_relate:
        ∀ p, priq p → (Abs p nil ↔ delete_max p = None).
  Axiom delete_max_Some_priq:
      ∀ p q k, priq p → delete_max p = Some(k,q) → priq q.
  Axiom delete_max_Some_relate:
  ∀ (p q: priqueue) k (pl ql: list key), priq p →
   Abs p pl →
   delete_max p = Some (k,q) →
   Abs q ql →
   Permutation pl (k::ql) ∧ Forall (ge k) ql.
  Axiom merge_priq: ∀ p q, priq p → priq q → priq (merge p q).
  Axiom merge_relate:
    ∀ p q pl ql al, 
       priq p → priq q →
       Abs p pl → Abs q ql → Abs (merge p q) al →
       Permutation al (pl++ql).
End PRIQUEUE.Module Type PRIQUEUE.
  Parameter priqueue: Type.
  Definition key := nat.
  Parameter empty: priqueue.
  Parameter insert: key → priqueue → priqueue.
  Parameter delete_max: priqueue → option (key * priqueue).
  Parameter merge: priqueue → priqueue → priqueue.
  Parameter priq: priqueue → Prop.
  Parameter Abs: priqueue → list key → Prop.
  Axiom can_relate: ∀ p, priq p → ∃ al, Abs p al.
  Axiom abs_perm: ∀ p al bl, 
   priq p → Abs p al → Abs p bl → Permutation al bl.
  Axiom empty_priq: priq empty.
  Axiom empty_relate: Abs empty nil.
  Axiom insert_priq: ∀ k p, priq p → priq (insert k p).
  Axiom insert_relate:
        ∀ p al k, priq p → Abs p al → Abs (insert k p) (k::al).
  Axiom delete_max_None_relate:
        ∀ p, priq p → (Abs p nil ↔ delete_max p = None).
  Axiom delete_max_Some_priq:
      ∀ p q k, priq p → delete_max p = Some(k,q) → priq q.
  Axiom delete_max_Some_relate:
  ∀ (p q: priqueue) k (pl ql: list key), priq p →
   Abs p pl →
   delete_max p = Some (k,q) →
   Abs q ql →
   Permutation pl (k::ql) ∧ Forall (ge k) ql.
  Axiom merge_priq: ∀ p q, priq p → priq q → priq (merge p q).
  Axiom merge_relate:
    ∀ p q pl ql al, 
       priq p → priq q →
       Abs p pl → Abs q ql → Abs (merge p q) al →
       Permutation al (pl++ql).
End PRIQUEUE.




List PriQueue
Definition key := nat.
Definition priqueue := list key.
Definition empty : priqueue := nil.
Definition insert (k: key)(p: priqueue) := k::p.
Definition delete_max (p: priqueue) :=
  match p with
  | i::p' ⇒ Some (select i p')
  | nil ⇒ None
end.
Definition merge (p q: priqueue) : priqueue := p++q.

inv true





Definition priqueue := list tree.
Definition empty : priqueue := nil.
Definition smash (t u: tree) : tree :=
  match t , u with
  | Node x t1 Leaf, Node y u1 Leaf ⇒
                   if x >? y then Node x (Node y u1 t1) Leaf
                                else Node y (Node x t1 u1) Leaf
  | _ , _ ⇒ Leaf (* arbitrary bogus tree *)
  end.
Fixpoint carry (q: list tree) (t: tree) : list tree :=
  match q, t with
  | nil, Leaf ⇒ nil
  | nil, _ ⇒ t :: nil
  | Leaf :: q', _ ⇒ t :: q'
  | u :: q', Leaf ⇒ u :: q'
  | u :: q', _ ⇒ Leaf :: carry q' (smash t u)
 end.
Definition insert (x: key) (q: priqueue) : priqueue :=
     carry q (Node x Leaf Leaf).
Eval compute in fold_left (fun x q ⇒insert q x) [3;1;4;1;5;9;2;3;5] empty.
    = [Node 5 Leaf Leaf;
       Leaf;
       Leaf;
       Node 9
          (Node 4 (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf))
             (Node 3 (Node 2 Leaf Leaf) (Node 5 Leaf Leaf)))
          Leaf]
     : priqueue
Fixpoint join (p q: priqueue) (c: tree) : priqueue :=
  match p, q, c with
    [], _ , _ ⇒ carry q c
  | _, [], _ ⇒ carry p c
  | Leaf::p', Leaf::q', _ ⇒ c :: join p' q' Leaf
  | Leaf::p', q1::q', Leaf ⇒ q1 :: join p' q' Leaf
  | Leaf::p', q1::q', Node _ _ _ ⇒ Leaf :: join p' q' (smash c q1)
  | p1::p', Leaf::q', Leaf ⇒ p1 :: join p' q' Leaf
  | p1::p', Leaf::q',Node _ _ _ ⇒ Leaf :: join p' q' (smash c p1)
  | p1::p', q1::q', _ ⇒ c :: join p' q' (smash p1 q1)
 end.
Fixpoint unzip (t: tree) (cont: priqueue → priqueue) : priqueue :=
  match t with
  | Node x t1 t2 ⇒ unzip t2 (fun q ⇒ Node x t1 Leaf :: cont q)
  | Leaf ⇒ cont nil
  end.
Definition heap_delete_max (t: tree) : priqueue :=
  match t with
    Node x t1 Leaf ⇒ unzip t1 (fun u ⇒ u)
  | _ ⇒ nil (* bogus value for ill-formed or empty trees *)
  end.
Fixpoint find_max' (current: key) (q: priqueue) : key :=
  match q with
  | [] ⇒ current
  | Leaf::q' ⇒ find_max' current q'
  | Node x _ _ :: q' ⇒ find_max' (if x >? current then x else current) q'
  end.
Fixpoint find_max (q: priqueue) : option key :=
  match q with
  | [] ⇒ None
  | Leaf::q' ⇒ find_max q'
  | Node x _ _ :: q' ⇒ Some (find_max' x q')
 end.
Fixpoint delete_max_aux (m: key) (p: priqueue) : priqueue * priqueue :=
  match p with
  | Leaf :: p' ⇒ let (j,k) := delete_max_aux m p' in (Leaf::j, k)
  | Node x t1 Leaf :: p' ⇒
       if m >? x
       then (let (j,k) := delete_max_aux m p'
             in (Node x t1 Leaf::j,k))
       else (Leaf::p', heap_delete_max (Node x t1 Leaf))
  | _ ⇒ (nil, nil) (* Bogus value *)
  end.
Definition delete_max (q: priqueue) : option (key * priqueue) :=
  match find_max q with
  | None ⇒ None
  | Some m ⇒ let (p',q') := delete_max_aux m q
                            in Some (m, join p' q' Leaf)
  end.
  Definition merge (p q: priqueue) := join p q Leaf.

a



    t is a complete binary tree of depth n, with every key <= m
Fixpoint pow2heap' (n: nat) (m: key) (t: tree) :=
  match n, m, t with
    0, m, Leaf ⇒ True
  | 0, m, Node _ _ _ ⇒ False
  | S _, m,Leaf ⇒ False
  | S n', m, Node k l r ⇒
      m ≥ k ∧ pow2heap' n' k l ∧ pow2heap' n' m r
end.
  t is a power-of-2 heap of depth n

Definition pow2heap (n: nat) (t: tree) :=
  match t with
    Node m t1 Leaf ⇒ pow2heap' n m t1
  | _ ⇒ False
end.
  l is the ith tail of a binomial heap


Fixpoint priq' (i: nat) (l: list tree) : Prop :=
  match l with
  | t :: l' ⇒ (t=Leaf ∨ pow2heap i t) ∧ priq' (S i) l'
  | nil ⇒ True
end.
  q is a binomial heap
  Definition priq (q: priqueue) : Prop := priq' 0 q.
