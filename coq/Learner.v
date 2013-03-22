Require Import Omega.

Definition function := nat -> nat.
Hint Unfold function.

Module Type LearningDomain.
  Parameter function_spec : Set.
  Parameter function_spec_dec :
    forall (x y:function_spec),
      { x = y } + { x <> y }.
  Parameter function_spec_eval :
    function_spec -> function.
End LearningDomain.

Module Learning ( Export Domain : LearningDomain ).
  Inductive query : Set :=
  | membership : nat -> query
  | correct    : function_spec -> query.
  Hint Constructors query.

  Inductive answer : query -> Set :=
  | membership_answer : forall (x y:nat),
    answer (membership x)
  | correct_answer_counter : forall f (x y:nat),
    answer (correct f)
  | correct_answer_good : forall f,
    answer (correct f).
  Hint Constructors answer.

  Definition Oracle := forall (q:query), answer q.
  Hint Unfold Oracle.

  Definition Oracle_correct (f:function_spec) (o:Oracle) :=
    (forall x y,
      o (membership x) = membership_answer x y -> 
      (function_spec_eval f) x = y)
    /\ (forall f' x y, 
      o (correct f') = correct_answer_counter f' x y -> 
      (function_spec_eval f') x <> y
      /\ (function_spec_eval f) x = y)
    /\ (forall f', 
      o (correct f') = correct_answer_good f'
      -> forall x,
        (function_spec_eval f') x = (function_spec_eval f) x).
  Hint Unfold Oracle_correct.

  Definition Learner := Oracle -> function_spec.
  Hint Unfold Learner.

  Definition Learner_correct (o:Oracle) (l:Learner) :=
    forall f,
      Oracle_correct f o ->
      forall x,
        (function_spec_eval (l o)) x = (function_spec_eval f) x.
  Hint Unfold Learner_correct.
End Learning.

Require Import List.

Module LagrangeLD <: LearningDomain.
  Definition function_spec := list (nat*nat).

  Theorem function_spec_dec :
    forall (x y:function_spec),
      { x = y } + { x <> y }.
  Proof.
    decide equality. decide equality.
    decide equality. decide equality.
  Qed.

  Theorem nat_eq_dec:
    forall (x y:nat),
      { x = y } + { x <> y }.
  Proof.
    decide equality.
  Qed.

  Fixpoint function_spec_eval (ps:list (nat*nat)) x' :=
    match ps with
      | nil =>
        0
      | (x,y) :: ps =>
        if nat_eq_dec x x' then
          y
          else
            function_spec_eval ps x'
    end.  
End LagrangeLD.

Module Import LagrangeLearning := Learning LagrangeLD.

Theorem lagrange_counter_example :
  forall ps ps',
    ps <> ps' ->
    { x | function_spec_eval ps x <> function_spec_eval ps' x }.
Proof.
Admitted.

Definition lagrange_oracle (ps:list (nat*nat)) (q:query) : answer q :=
match q with
| membership x =>
  membership_answer x ((function_spec_eval ps) x) 
| correct ps' =>
  match function_spec_dec ps ps' with
    | left _ =>
      correct_answer_good ps'
    | right NEQ  =>
      match lagrange_counter_example ps ps' NEQ with
        | exist x _ =>
          correct_answer_counter ps' x ((function_spec_eval ps) x)
      end
  end
end.

Theorem lagrange_oracle_correct :
  forall ps,
    Oracle_correct ps (lagrange_oracle ps).
Proof.
  intros cs. unfold Oracle_correct, lagrange_oracle.
  split; [|split]; simpl.

  intros x y EQ. inversion_clear EQ. reflexivity.

  intros cs' x y.
  destruct (function_spec_dec cs cs') as [EQ | NEQ].
  intros H. inversion H.
  destruct (lagrange_counter_example cs cs' NEQ) as [z CEX].
  intros H. inversion H. subst x y. auto.

  intros cs'. destruct (function_spec_dec cs cs') as [EQ | NEQ].
  subst cs'. auto.
  destruct (lagrange_counter_example cs cs' NEQ) as [z CEX].
  intros H. inversion H.
Qed.

(* The idea is that we are constructing a Lagrangian Polynomial for
the data and whenever we're wrong, there's another data point we
should have added. The number represents the degree of the polynomial,
or the number of data points. The ps should have the invariant that
they are all valid readings of the function. *)

Fixpoint lagrange_learner (ps:list (nat*nat)) (n:nat) (o:Oracle) :=
match n with 
| 0 =>
  ps
| S n =>
  match o (correct ps) with
    | correct_answer_good _ =>
      ps
    | correct_answer_counter _ x y =>
      lagrange_learner ((x,y)::ps) n o
  end
end.

Theorem lagrange_equality :
  forall ps l,
    (length ps) = (length l) ->
    (forall x y, In (x,y) l -> function_spec_eval ps x = y) ->
    forall x,
      function_spec_eval ps x = function_spec_eval l x.
Proof.
 (* The intuition is that 
Admitted.

Theorem lagrange_learner_correct_general :
  forall n ps l,
      (length ps) <= (length l) + n ->
      (forall x y, In (x,y) l -> function_spec_eval ps x = y) ->
      Learner_correct (lagrange_oracle ps) (lagrange_learner l n).
Proof.
  induction n as [|n]; simpl.

  intros ps l LEN Pl f. 
  intros [member_correct [correct_good_correct correct_counter_correct]].
  remember (function_spec_dec ps l) as DEC.
  destruct DEC as [EQ|NEQ].
  eapply correct_counter_correct. simpl.
  rewrite <- HeqDEC. reflexivity.

  symmetry. eapply member_correct. simpl.

  induction l as [|[x y] l].
   destruct ps as [|p ps].
    symmetry. apply member_correct. reflexivity.
    simpl in LEN. inversion LEN.
   simpl.
   destruct (nat_eq_dec x x').
    symmetry. apply member_correct. simpl.
    replace x'. erewrite Pl. reflexivity.
    simpl. auto.

    eapply IHl.
    intros xx yy IN.
    apply Pl. simpl. auto.

  intros ps l LEN. unfold Learner_correct.
  intros Pl.
  intros f.
  intros [member_correct [correct_good_correct correct_counter_correct]].
  intros x.
  simpl.
  destruct (function_spec_dec ps l).
  simpl. symmetry. apply member_correct. simpl.
  rewrite e. reflexivity.
  destruct (lagrange_counter_example ps l n0) as [x' NEQ].
  eapply IHn.
  
  admit.

  intros xx yy Inl.
  eapply Pl. simpl in Inl.
  destruct Inl as [ EQ | Inl ]; auto.
  inversion EQ. subst xx yy. clear EQ.


Admitted.

Theorem lagrange_learner_correct :
  forall ps,
    Learner_correct
     (lagrange_oracle ps)
     (lagrange_learner nil (length ps)).
Proof.
  intros ps. eapply lagrange_learner_correct_general.
  auto.
  intros x y IN. inversion IN.
Qed.
