Set Implicit Arguments.

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).
End ilist.

Implicit Arguments Nil [A].

Fixpoint izip A B n (l1 : ilist A n) : ilist B n -> ilist (A * B) n := 
  match l1 with
    | Nil => fun l2 => Nil
    | Cons _ x l1' =>
      fun l2 (* : ilist B n *) => 
        (match l2 in ilist _ n' 
               return (ilist A (pred n') ->
                       match n' with
                         | O => unit
                         | S _ => ilist (A * B) n'
                       end) with 
          | Nil => fun l1' => tt
          | Cons _ y l2' => fun l1' => Cons (x,y) (izip l1' l2')
        end) l1'
  end.

Hint Constructors ilist.
Theorem izip' : 
  forall A B n,
    ilist A n -> ilist B n -> ilist (A * B) n.
Proof.
  intros A B n l1.
  induction l1 as [|n1 a l1']; intros l2; inversion l2 as [|n2 b l2']; eauto.
Qed.

Extraction izip.

Set Extraction AccessOpaque.
Extraction izip'.
