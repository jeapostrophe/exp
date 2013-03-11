Require Omega.   (* needed for using the [omega] tactic *)
Require Export Bool.
Require Export List.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

Definition id := nat.
Hint Unfold id.

Definition beq_id := beq_nat.
Hint Unfold beq_id.

Definition state := id -> nat.
Hint Unfold state.

Definition empty_state : state :=
  fun _ => 0.
Hint Unfold empty_state.

Definition update (st : state) (X:id) (n : nat) : state :=
  fun X' => if beq_id X X' then n else st X'.
Hint Unfold update.

Inductive aexp : Type :=
| ANum : nat -> aexp
| AId : id -> aexp
| APlus : aexp -> aexp -> aexp.
Hint Constructors aexp.

Inductive aeval : state -> aexp -> nat -> Prop :=
| ANum_eval :
  forall s n,
    aeval s (ANum n) n
| AId_eval :
  forall s i,
    aeval s (AId i) (s i)
| APlus_eval :
  forall s le lv re rv,
    aeval s le lv ->
    aeval s re rv ->
    aeval s (APlus le re) (lv + rv).
Hint Constructors aeval.

Theorem aeval_det:
 forall s ae n_0 n_1,
   aeval s ae n_0 ->
   aeval s ae n_1 ->
   n_0 = n_1.
Proof.
  intros s ae n_0 n_1 A1. generalize dependent n_1.
  induction A1; intros n_1 A2; inversion A2; subst; auto.
Qed.
Hint Resolve aeval_det.

Inductive bexp : Type :=
| BEq : aexp -> aexp -> bexp.
Hint Constructors bexp.

Inductive beval : state -> bexp -> bool -> Prop :=
| BEq_eval :
  forall s le lv re rv,
    aeval s le lv ->
    aeval s re rv ->
    beval s (BEq le re) (beq_nat lv rv).
Hint Constructors beval.

Theorem beval_det:
 forall s be b_0 b_1,
   beval s be b_0 ->
   beval s be b_1 ->
   b_0 = b_1.
Proof.
  intros s ae n_0 n_1 A1. generalize dependent n_1.
  induction A1; intros n_1 A2; inversion A2; subst; eauto.
Qed.
Hint Resolve beval_det.

Inductive com : Type :=
| CAss : id -> aexp -> com
| CIf : bexp -> com -> com -> com.
Hint Constructors com.

Inductive ceval : state -> com -> state -> Prop :=
| CAss_eval :
  forall s i ae v,
    aeval s ae v ->
    ceval s (CAss i ae) (update s i v)
| CIf_true_eval :
  forall s be ct cf s',
    beval s be true ->
    ceval s ct s' ->
    ceval s (CIf be ct cf) s'
| CIf_false_eval :
  forall s be ct cf s',
    beval s be false ->
    ceval s cf s' ->
    ceval s (CIf be ct cf) s'.
Hint Constructors ceval.

Theorem ceval_det:
  forall s c s_0 s_1,
    ceval s c s_0 ->
    ceval s c s_1 ->
    s_0 = s_1.
Proof.
  intros s c s_0 s_1 C1. generalize dependent s_1.
  induction C1; intros s_1 C2; inversion C2; subst; eauto.
  absurd (true = false).
   intros TF. inversion TF.
   eapply beval_det. apply H. apply H5.
  absurd (false = true).
   intros TF. inversion TF.
   eapply beval_det. apply H. apply H5.
Qed.
Hint Resolve ceval_det.

Definition thread := list com.
Hint Unfold thread.

Inductive teval : state -> thread -> state -> thread -> Prop :=
| fst_eval :
  forall s c_0 ts s',
    ceval s c_0 s' ->
    teval s (c_0::ts) s' ts.
Hint Constructors teval.

Theorem teval_det:
  forall s t s_0 t_0 s_1 t_1,
    teval s t s_0 t_0 ->
    teval s t s_1 t_1 ->
    (s_0 = s_1) /\ (t_0 = t_1).
Proof.
  intros s t s_0 t_0 s_1 t_1 T1.
   generalize dependent s_1. 
   generalize dependent t_1.
  induction T1 as [s c_0 ts s' C].
  intros t_1 s_1 T2. inversion T2; subst; eauto.
Qed.
Hint Resolve teval_det.

Inductive tseval_nondet : state -> list thread -> state -> Prop :=
| Done_nondet :
  forall s ts,
  (forall t,
    In t ts -> ~ (exists s' t', teval s t s' t')) ->
  tseval_nondet s ts s
| Thread_nondet:
  forall s t s' t' ts ts_before ts_after s'',
    teval s t s' t' ->
    ts = ts_before ++ t :: ts_after ->
    tseval_nondet s' (ts_before ++ t' :: ts_after) s'' ->
    tseval_nondet s ts s''.
Hint Constructors tseval_nondet.

Theorem tseval_nondet_is:
  exists s ts s' s'',
    tseval_nondet s ts s'
    /\ tseval_nondet s ts s''
    /\ s' <> s''.
Proof.
  exists empty_state.
  exists (((CAss 0 (ANum 1))::nil) :: ((CAss 0 (ANum 2))::nil) :: nil).
  exists (update (update empty_state 0 2) 0 1).
  exists (update (update empty_state 0 1) 0 2).
  split; [idtac | split].

  eapply Thread_nondet with (ts_before:=((CAss 0 (ANum 1))::nil)::nil); 
    [idtac|reflexivity|idtac].
  eapply fst_eval.
  eapply CAss_eval.
  eapply ANum_eval.
  eapply Thread_nondet with (ts_before:=nil);
        [idtac|reflexivity|idtac].
  eapply fst_eval.
  eapply CAss_eval.
  eapply ANum_eval.
  eapply Done_nondet.
  simpl. intros t [EQnil | [EQnil | F]]; subst; try (inversion F);
   intros [s' [t' TE]]; inversion TE.

  eapply Thread_nondet with (ts_before:=nil);
    [idtac|simpl; reflexivity|idtac].
  eapply fst_eval.
  eapply CAss_eval.
  eapply ANum_eval.
  eapply Thread_nondet with (ts_before:=nil :: nil);
        [idtac|simpl; reflexivity|idtac].
  eapply fst_eval.
  eapply CAss_eval.
  eapply ANum_eval.
  eapply Done_nondet.
  simpl. intros t [EQnil | [EQnil | F]]; subst; try (inversion F);
   intros [s' [t' TE]]; inversion TE.

  intros HF.
  absurd (1 = 2).
   intros HEQ. inversion HEQ.
   replace 2 with ((update (update empty_state 0 1) 0 2) 0).
   rewrite <- HF.
   reflexivity.
   reflexivity.
Qed.

Theorem tseval_nondet_isn:
   ~ ( forall s ts s' s'',
        tseval_nondet s ts s' ->
        tseval_nondet s ts s'' ->
        s' = s'' ).
Proof.
  intros H.
  destruct tseval_nondet_is as [s [ts [s' [s'' [E1 [E2 EQ]]]]]].
  apply EQ.
  eapply H. apply E1. apply E2.
Qed.

Definition schedule := list nat.
Hint Unfold schedule.

Inductive tseval_det : schedule -> state -> list thread -> state -> Prop :=
| Done_det :
  forall sch s ts,
  (forall t,
    In t ts -> ~ (exists s' t', teval s t s' t')) ->
  tseval_det sch s ts s
| Thread_det:
  forall s t s' t' ts sch_0 ts_before ts_after sch_n s'',
    teval s t s' t' ->
    ts = ts_before ++ t :: ts_after ->
    length ts_before = sch_0 ->
    tseval_det sch_n s' (ts_before ++ t' :: ts_after) s'' ->
    tseval_det (sch_0 :: sch_n) s  ts  s''.
Hint Constructors tseval_det.

Lemma app_length:
  forall X (l1:list X) l3 l2 l4,
    length l1 = length l3 ->
    l1 ++ l2 = l3 ++ l4 ->
    l1 = l3.
Proof.
  intros X. induction l1 as [|x l1]; induction l3 as [|y l3]; simpl;
  intros l2 l4 EQ; inversion EQ; auto.
  intros EQ2. inversion EQ2; subst.
  erewrite IHl1. reflexivity.
  auto. exact H2.
Qed.

Lemma app_tail:
  forall X (l1:list X) x1 x2 l2 l3,
    l1 ++ x1 :: l2 = l1 ++ x2 :: l3 ->
    x1 = x2.
Proof.
  intros X. induction l1 as [|x0 l1]; 
   simpl; intros x1 x2 l2 l3 EQ; inversion EQ; subst; eauto.
Qed.

Theorem tseval_det_is:
  forall sch s ts s' s'',
    tseval_det sch s ts s' ->
    tseval_det sch s ts s'' ->
    s' = s''.
Proof.
  intros sch s ts s' s'' E1. generalize dependent s''.
  induction E1 as [sch s ts NoRun|s t s' t' ts sch_0 ts_before ts_after sch_n s'' T1 TEQ LEQ E1]; intros s''' E2; inversion E2; subst.
   reflexivity.

   assert False. eapply NoRun with (t0:=t).
   apply in_or_app. right. simpl. auto.
   exists s'. exists t'. assumption.
   inversion H0.

   assert False. eapply H with (t0:=t).
   apply in_or_app. right. simpl. auto.
   exists s'. exists t'. assumption.
   inversion H0.

   eapply IHE1. 
   replace ts_before0 with ts_before in *; eauto.
   replace t0 with t in *; eauto.
   replace ts_after0 with ts_after in *; eauto.
   replace s'0 with s' in *; eauto.
   replace t'0 with t' in *; eauto.
   eapply teval_det; eauto.
   eapply teval_det; eauto.
    apply app_inv_head in H2.
    inversion H2. auto.

   eapply app_tail.
    exact H2.

   symmetry.
    erewrite app_length.
    reflexivity. 
    symmetry. apply H3.
    exact H2.
Qed. 

Theorem tseval_non_to_det:
  forall s ts s',
    tseval_nondet s ts s' ->
    exists sch,
      tseval_det sch s ts s'.
Proof.
  intros s ts s' TND.
  induction TND 
   as [s ts NoRun|s c_0 s' ts ts_before c_n ts_after s'' C EQts N].

  exists nil.
  eapply Done_det.
  apply NoRun.

  destruct IHN as [sch_n IHN].
  eexists.
  eapply Thread_det.
  apply C.
  apply EQts.
  reflexivity.
  apply IHN.
Qed.

Theorem tseval_det_to_non:
  forall sch s ts s',
    tseval_det sch s ts s' ->
    tseval_nondet s ts s'.
Proof.
  intros sch s ts s' TD.
  induction TD as [s ts ts' NoRun|s c_0 s' ts sch_0 ts_before c_n ts_after  sch_n s'' C EQts LENtsb N].

  eapply Done_nondet.
  apply NoRun.

  eapply Thread_nondet.
  apply C.
  apply EQts.
  apply IHN.
Qed.
