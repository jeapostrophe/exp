Require Import Omega.

Definition function := nat -> nat.
Hint Unfold function.

Inductive query : Set :=
| membership : nat -> query
| correct    : function -> query.
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
  /\ (forall f' x y, o (correct f') = correct_answer_counter f' x y -> f' x <> y /\ f x = y)
  /\ (forall f', o (correct f') = correct_answer_good f' -> forall x, f' x = f x)
.
Hint Unfold Oracle_correct.

Definition Learner := Oracle -> function.
Hint Unfold Learner.

Definition Learner_correct (o:Oracle) (l:Learner) :=
  forall f,
    Oracle_correct f o ->
    forall x,
      (l o) x = f x.
Hint Unfold Learner_correct.

Axiom function_equality_dec :
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
