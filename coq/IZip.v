Inductive list (X:Type) : Type :=
| nil : list X
| cons : forall (x:X) (l:list X),
           list X.

Fixpoint length {X:Type} (l:list X) :=
match l with
| nil => 0
| cons _ l =>
  S (length l)
end.

Fixpoint zip A B (l1:list A) (l2:list B) : list (A*B) :=
match l1 with
| nil => nil (A*B)
| cons x l1' =>
  match l2 with
      | nil => nil (A*B)
      | cons y l2' =>
        cons (A*B) (x, y) (zip A B l1' l2')
  end
end.

Inductive ilist (X:Set) : nat -> Set :=
| Nil : ilist X 0
| Cons : forall n (x:X),
           ilist X n ->
           ilist X (S n).

Fixpoint erase {X:Set} {n:nat} (l:ilist X n) : list X :=
match l with
| Nil => nil X
| Cons _ x l =>
  cons X x (erase l)
end.

Lemma erase_len :
  forall X n (l:ilist X n),
    length (erase l) = n.
Proof.
  intros X. induction n as [|n].
  intros l. inversion l.

Theorem izip :
  forall A B n (l1 : ilist A n) (l2 : ilist B n),
    { l3 : ilist (A*B) n |
      zip A B (erase l1) (erase l2) = erase l3  }.
Proof.
  intros A B.
  induction n as [|n]; simpl.

  intros l1 l2. exists (Nil (A*B)).
  

  destruct l1. Focus 2.

  destruct l1.
  inversion l1.

  induction l1 as [|n1 e1 l1]; simpl.

  intros l2. exists (Nil (A*B)). simpl. trivial.

  induction l2 as [|n2 e2 l2]; simpl.

  exists (Nil (A*B)). simpl. trivial.

  

Fixpoint izip A B n (l1 : ilist A n) : ilist B n -> ilist (A * B) n := 
  match l1 with
    | Nil => fun l2 => Nil (A*B)
    | Cons _ x l1' =>
      fun l2 (* : ilist B n *) => 
        (match l2 in ilist _ n' 
               return (ilist A (pred n') ->
                       match n' with
                         | O => unit
                         | S _ => ilist (A * B) n'
                       end) with 
          | Nil => fun l1' => tt
          | Cons _ y l2' => fun l1' => Cons (A*B) n (x,y) (izip A B n l1' l2')
        end) l1'
  end.
