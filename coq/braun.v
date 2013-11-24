Require Import Omega.

Set Implicit Arguments.

Variable A : Type.

Inductive braun_tree : nat -> Type :=
  | Empty : braun_tree 0
  | Node : forall (x:A) s_size t_size, 
             t_size <= s_size <= t_size+1 ->
             braun_tree s_size -> braun_tree t_size ->
             braun_tree (s_size+t_size+1).
Hint Constructors braun_tree.

Inductive copy2_spec : 
  forall (n:nat), 
    A -> braun_tree (S n) ->
    braun_tree n -> Prop :=
| c2s0 : 
    forall x,
      @copy2_spec 0 x (@Node x 0 0 _ Empty Empty) Empty
.
Axiom copy2_spec_dec:
  forall n x,
    { st | @copy2_spec n x (fst st) (snd st) }.

Inductive copy_spec (n:nat) : A -> braun_tree n -> Prop :=
| cs0 : forall x s t,
        copy2_spec x s t ->
        copy_spec x t.
Hint Constructors copy_spec.

Theorem copy_spec_dec :
  forall n x,
    { t | @copy_spec n x t }.
Proof.
  intros n x.
  destruct (copy2_spec_dec n x) as [ [s t] P ].
  eauto.
Qed.
  
