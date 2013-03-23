Require Import Omega.

Module Type LearningDomain.
  Parameter function_spec : Set.
  Parameter function_spec_dec :
    forall (x y:function_spec),
      { x = y } + { x <> y }.
  Parameter Dom : Set.
  Parameter Rng : Set.
  Definition function := Dom -> Rng.
  Parameter function_spec_eval :
    function_spec -> function.
End LearningDomain.

Module Learning ( Export Domain : LearningDomain ).
  Definition Oracle_membership := Dom -> Rng.
  Definition Oracle_membership_good 
    (f:function_spec) (om:Oracle_membership) :=
    forall x y,
      om x = y -> function_spec_eval f x = y.

  Definition Oracle_correct := function_spec -> unit + (Dom*Rng).
  Definition Oracle_correct_right_good
    (f:function_spec) (oc:Oracle_correct) :=
    forall f' x y,
      oc f' = inr (x,y) ->
      function_spec_eval f' x <> y
      /\ y = function_spec_eval f x.
  Definition Oracle_correct_left_good 
    (f:function_spec) (oc:Oracle_correct) :=
    forall f',
      oc f' = inl tt ->
      forall x,
        function_spec_eval f' x = function_spec_eval f x.
  Definition Oracle_correct_good
    (f:function_spec) (oc:Oracle_correct) :=
    (Oracle_correct_left_good f oc) /\
    (Oracle_correct_right_good f oc).

  Definition Oracle := (Oracle_membership * Oracle_correct)%type.
  Definition Oracle_good
    (f:function_spec) (o:Oracle) :=
    (Oracle_membership_good f (fst o))
    /\ (Oracle_correct_good f (snd o)).

  Definition Learner := Oracle -> function_spec.
  Hint Unfold Learner.

  Definition Learner_good (P:function_spec -> Prop) (learner:Learner) :=
    forall o f,
      P f ->
      Oracle_good f o ->
      forall x,
        (function_spec_eval (learner o)) x = (function_spec_eval f) x.
  Hint Unfold Learner_good.
End Learning.

Module Type Learner ( Export Domain : LearningDomain ).
  Module Export L := Learning Domain.

  Parameter learner : Learner.
  Parameter Learner_P : function_spec -> Prop.
  Parameter learner_good : Learner_good Learner_P learner.
End Learner.

Module ConstantLD <: LearningDomain.
  Parameter Dom : Set.
  Parameter Dom_0 : Dom.

  Parameter Rng : Set.
  Parameter Rng_0 : Rng.

  Parameter Rng_dec :
    forall (x y:Rng),
      { x = y } + { x <> y }.

  Definition function := Dom -> Rng.

  Definition function_spec := Rng.

  Theorem function_spec_dec :
    forall (x y:function_spec),
      { x = y } + { x <> y }.
  Proof.
    apply Rng_dec.
  Qed.

  Definition function_spec_eval (p:Rng) (x:Dom) : Rng := p.
End ConstantLD.

Module ConstantLearner <: Learner ConstantLD.
  Module Export L := Learning ConstantLD.

  Definition learner (o:Oracle) :=
    match (snd o) Rng_0 with
      | inl _ =>
        Rng_0
      | inr (x,y) =>
        y
    end.

  Definition Learner_P (f:function_spec) := True.

  Theorem learner_good : Learner_good Learner_P learner.
  Proof.
    intros [om oc] f Pf [om_g [oc_lg oc_rg]] x.
    unfold learner. simpl in *.
    remember (oc Rng_0) as oc0.
    destruct oc0.
   
    apply oc_lg. rewrite <- Heqoc0. destruct u; auto.

    destruct p as [xx yy].
    symmetry in Heqoc0.
    eapply oc_rg in Heqoc0.
    destruct Heqoc0 as [NEQ EQ].
    subst yy. unfold function_spec_eval.
    reflexivity.
  Qed.
End ConstantLearner.

(* XXX Can't figure out how to instantiate ConstantLD with Dom = Rng =
nat *)

(* lagrange takes a set of data points and produces the Lagrangian
polynomial that hits them exactly *)
Axiom lagrange : list (nat*nat) -> nat -> nat.

(* the learner relies on the idea that if the oracle has said it is
correct on (S N) data points, then it is correct for polynomials up
degree N, or update to N data points. *)

(* this idea is captured in this axiom: if a list of points if
accurate, then adding more accurate points can't hurt it *)

Axiom lagrange_monotone:
  forall ps y f x,
  lagrange ps y = lagrange f y ->
  lagrange ((x, lagrange f x) :: ps) y = lagrange f y.

Require Import List.

Definition lagrange_correct f (n:nat) ps :=
  (exists f_rst,
    length f_rst = n
    /\ length f = length f_rst + length ps
    /\ (forall x y, In (x,y) (f_rst++ps) -> (lagrange f) x = y))
  /\ (forall x, (lagrange ps) x = (lagrange f) x).

Theorem lagrange_step:
  forall f n ps x,
    lagrange_correct f (S n) ps ->
    lagrange_correct f n ((x, lagrange f x)::ps).
Proof.
  intros f n ps x.
  intros [[f_rst [LEN_frst [LENf IN]]] EQ].
  unfold lagrange_correct.
  
  destruct f_rst as [|[xx yy] f_rst]; simpl in LEN_frst;
    inversion LEN_frst.
  clear LEN_frst.
  rename H0 into LEN_frst.
  simpl in LENf.
  split. exists f_rst.
  split. reflexivity.
  split. simpl. rewrite LENf. omega.
  intros xx' yy'.
  rewrite in_app_iff. simpl.
  simpl in IN.
  intros [IN_fst | [EQ' | IN_ps]].
  apply IN. rewrite in_app_iff. auto.
  inversion EQ'. subst xx' yy'. reflexivity.
  apply IN. rewrite in_app_iff. auto.

  intros xx'.
  apply lagrange_monotone.
  apply EQ.
Qed.

Module PolyLD <: LearningDomain.
  Definition function_spec := list (nat*nat).
  Theorem function_spec_dec:
    forall (x y:function_spec),
      { x = y } + { x <> y }.
  Proof.
    decide equality. decide equality.
    decide equality. decide equality.
  Qed.
  Definition Dom := nat.
  Definition Rng := nat.
  Definition function := Dom -> Rng.
  Definition function_spec_eval (fs:function_spec) := lagrange fs.
End PolyLD.

Module PolyLearner <: Learner PolyLD.
  Module Export L := Learning PolyLD.

  Fixpoint learner (ps:list (nat*nat)) (n:nat) (o:Oracle) :=
    match n with
      | 0 =>
        ps
      | S n =>
        match (snd o) ps with
          | inl _ =>
            ps
          | inr (x, y) =>
            learner ((x,y)::ps) n o
        end
    end.

  Theorem learner_good : 
    forall n ps,
      Learner_good (fun f => lagrange_correct f n ps) (learner ps n).
  Proof.
    unfold Learner_good, function_spec_eval.
    induction n as [|n]; intros ps o f lc og x; simpl.

    apply lc.

    remember (snd o ps) as oc_ps.
    destruct oc_ps as [u|[xx yy]].
    apply lc.
    
    eapply IHn; try auto.
    destruct og as [om_g [ocl_g ocr_g]].
    symmetry in Heqoc_ps.
    eapply ocr_g in Heqoc_ps.
    destruct Heqoc_ps as [NEQ EQ].
    subst yy.
    apply lagrange_step. exact lc.
  Qed.

End PolyLearner.
