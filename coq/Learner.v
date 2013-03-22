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

  Definition Oracle_correct (f:function) (o:Oracle) :=
    (forall x y, o (membership x) = membership_answer x y -> f x = y)
    /\ (forall f' x y, o (correct f') = correct_answer_counter f' x y -> (function_spec_eval f') x <> y /\ f x = y)
    /\ (forall f', o (correct f') = correct_answer_good f' -> forall x, (function_spec_eval f') x = f x).
  Hint Unfold Oracle_correct.

  Definition Learner := Oracle -> function_spec.
  Hint Unfold Learner.

  Definition Learner_correct (o:Oracle) (l:Learner) :=
    forall f,
      Oracle_correct f o ->
      forall x,
        (function_spec_eval (l o)) x = f x.
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
  forall cs,
    Oracle_correct (function_spec_eval cs) (lagrange_oracle cs).
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

Definition lagrange_learner (o:Oracle) (ps:list (nat*nat)) (n:nat) :=
match n with 
| 0 =>
  ps
| S n =>
  match o (correct ps) with
    | correct_answer_good _ =>
      ps
    | correct_answer_counter _ x y =>
      lagrange_learner o ((x,y)::ps) n
  end
end.


  Axiom function_spec_dec :
    forall (f f':function), {x | f x <> f' x} + {f = f'}.

  Definition pipe_oracle (f:function) : Oracle :=
    fun q =>
      match q with
        | membership x =>
          membership_answer x (f x)
        | correct f' =>
          match function_equality_dec f f' with
            | inright _ =>
              correct_answer_good f'
            | inleft (exist x _) =>
              correct_answer_counter f' x (f x)
          end
      end.

  Definition pipe_learner (o:Oracle) :=
    fun x =>
      match o (membership x) with
        | membership_answer _ y =>
          y
        | _ =>
          0
      end.

  Theorem pipe_oracle_learner_correct:
    forall f,
      Learner_correct (pipe_oracle f) (pipe_learner).
  Proof.
    intros f.

    unfold Learner_correct, Oracle_correct, pipe_learner, pipe_oracle.

    intros f'.
    intros [membership_correct [correct_counter_correct correct_good_correct]].
    intros x.
    symmetry.
    eapply membership_correct.
    reflexivity.
  Qed.
