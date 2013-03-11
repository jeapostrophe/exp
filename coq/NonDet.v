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

Definition thread := list com.
Hint Unfold thread.

Inductive teval : state -> thread -> state -> thread -> Prop :=
| fst_eval :
  forall s c_0 ts s',
    ceval s c_0 s' ->
    teval s (c_0::ts) s' ts.
Hint Constructors teval.

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
   replace t0 with t in *.
   replace ts_before0 with ts_before in *.
   replace ts_after0 with ts_after in *.
   replace s'0

Admitted.

Theorem tseval_non_to_det:
  forall s ts s',
    tseval_nondet s ts s' ->
    exists sch,
      tseval_det sch s ts s'.
Proof.
  intros s ts s' TND.
  induction TND as [s c_0 s' ts ts_before c_n ts_after s'' C EQts N].
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
  induction TD as [s c_0 s' ts sch_0 ts_before c_n ts_after  sch_n s'' C EQts LENtsb N].
  eapply Thread_nondet.
  apply C.
  apply EQts.
  apply IHN.
Qed.
