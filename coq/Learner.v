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

Module PolyLD <: LearningDomain.
  Definition function_spec := list nat.

  Theorem function_spec_dec :
    forall (x y:function_spec),
      { x = y } + { x <> y }.
  Proof.
    decide equality. decide equality.
  Qed.

  Fixpoint function_spec_eval (coefficients:list nat) x :=
    match coefficients with
      | nil =>
        0
      | a :: more =>
        (a + x * (function_spec_eval more x))
    end.  

  Theorem all_zeros_dec :
    forall (l:list nat),
      { x | In x l /\ x <> 0 }
      + { forall x, In x l -> x = 0 }.
  Proof.
    induction l as [|x l].
    right. intros x IN. inversion IN.
    destruct x as [|x].
    destruct IHl as [[x [IN NZ]] | Z].
    left. exists x. simpl. auto.
    right. intros x. simpl. 
    intros [IS IN


  Theorem function_spec_eval_dec :
    forall (x y:function_spec),
      { z | function_spec_eval x z <> function_spec_eval y z }
      + { forall z, function_spec_eval x z = function_spec_eval y z }.
  Proof.
    induction x as [|c cs].
    induction y as [|c' cs'].

    right. intros z. simpl. auto.

    simpl in *.
    

    destruct IHcs' as [[z NEQ] | EQ].

    destruct z as [|z].


    destruct c' as [|c'].

    left. exists z.
    intros H. apply NEQ.
    rewrite H. simpl.

End PolyLD.

Module Import PolyLearning := Learning PolyLD.

Theorem poly_counter_example :
  forall cs cs',
    cs <> cs' ->
    { x | function_spec_eval cs x <> function_spec_eval cs' x }.
Proof.
  induction cs as [|c cs].
  induction cs' as [|c' cs'].
  
  intros H. absurd (@nil nat = nil); auto.

  intros NEQ. simpl.
  destruct c' as [|c']; simpl.

Definition poly_oracle (cs:list nat) (q:query) : answer q :=
match q with
| membership x =>
  membership_answer x ((function_spec_eval cs) x) 
| correct cs' =>
  match function_spec_dec cs' with
    | left _ =>
      correct_answer_good cs'
    | right _ =>
      match poly_counter_example cs cs' in
      correct_answer_counter f' x y
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
