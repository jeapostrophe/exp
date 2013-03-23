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

  Definition Learner_correct (learner:Learner) :=
    forall o f,
      Oracle_correct f o ->
      forall x,
        (function_spec_eval (learner o)) x = (function_spec_eval f) x.
  Hint Unfold Learner_correct.
End Learning.

Module Type Learner ( Export Domain : LearningDomain ).
  Module Export L := Learning Domain.

  Parameter learner : Learner.

  Parameter learner_correct : Learner_correct learner.
End Learner.

Module ConstantLD <: LearningDomain.
  Definition function_spec := nat.

  Theorem function_spec_dec :
    forall (x y:function_spec),
      { x = y } + { x <> y }.
  Proof.
    decide equality.
  Qed.

  Definition function_spec_eval (p:nat) (x:nat) := p.
End ConstantLD.

Module ConstantLearner <: Learner ConstantLD.
  Module Export L := Learning ConstantLD.

  Definition learner (o:Oracle) :=
    match o (correct 0) with
      | membership_answer _ _ =>
      (* XXX This case is impossible. It's strange that the type system doesn't rule it out *)
        0
      | correct_answer_good _ =>
        0
      | correct_answer_counter _ x y =>
        y
    end.

  Theorem learner_correct : Learner_correct learner.
  Proof.
    intros o k.
    unfold Learner_correct, Oracle_correct, learner, function_spec_eval.
    intros [m_c [cac_c cag_c]].
    intros x.
    remember k (correct 0).
    remember (function_spec_dec k 0) as EQ.
    destruct EQ.
    symmetry. eapply m_c. rewrite e. reflexivity.
    symmetry. eapply (cac_c 0). rewrite <- HeqEQ.
    reflexivity.

    Grab Existential Variables.
    apply 0.
  Qed.

End ConstantLearner.

Module Import ConstantLearning := Learning ConstantLD.

Definition constant_oracle (k:nat) (q:query) : answer q :=
  match q with
    | membership x =>
      membership_answer x k
    | correct k' =>
      match function_spec_dec k k' with
        | left _ =>
          correct_answer_good k'
        | right NEQ  =>
          correct_answer_counter k' 0 k
      end
  end.

Theorem constant_oracle_correct :
  forall k,
    Oracle_correct k (constant_oracle k).
Proof.
  intros k. unfold Oracle_correct, constant_oracle.
  split; [|split]; simpl.

  intros x y EQ. inversion_clear EQ.
  unfold function_spec_eval. reflexivity.

  intros k' x y.
  destruct (function_spec_dec k k') as [EQ | NEQ].
  intros H. inversion H.
  intros H. inversion H. subst x y. auto.

  intros k'. destruct (function_spec_dec k k') as [EQ | NEQ].
  subst k'. auto.
  intros H. inversion H.
Qed.
