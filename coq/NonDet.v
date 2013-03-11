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

Inductive tseval_nondet : state -> list thread -> state -> Prop :=
| Thread_nondet:
  forall s c_0 s' ts ts_before c_n ts_after s'',
    ceval s c_0 s' ->
    ts = ts_before ++ (c_0 :: c_n) :: ts_after ->
    tseval_nondet s' (ts_before ++ c_n :: ts_after) s'' ->
    tseval_nondet s ts s''.
Hint Constructors tseval_nondet.

Theorem tseval_nondet_is:
   ~ ( forall s ts s' s'',
        tseval_nondet s ts s' ->
        tseval_nondet s ts s'' ->
        s' = s'' ).
Proof.
Admitted.

Definition schedule := list nat.
Hint Unfold schedule.

Inductive tseval_det : schedule -> state -> list thread -> state -> Prop :=
| Thread_det:
  forall s c_0 s' ts sch_0 ts_before c_n ts_after sch_n s'',
    ceval s c_0 s' ->
    ts = ts_before ++ (c_0 :: c_n) :: ts_after ->
    length ts_before = sch_0 ->
    tseval_det sch_n s' (ts_before ++ c_n :: ts_after) s'' ->
    tseval_det (sch_0 :: sch_n) s  ts  s''.
Hint Constructors tseval_det.

Theorem tseval_det_is:
  forall sch s ts s' s'',
    tseval_det sch s ts s' ->
    tseval_det sch s ts s'' ->
    s' = s''.
Proof.
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
