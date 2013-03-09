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

Inductive tseval : state -> list thread -> state -> Prop :=
| Thread_eval:
  forall s c_0 s' ts ts_before c_n ts_after s'',
    ceval s c_0 s' ->
    ts = ts_before ++ (c_0 :: c_n) :: ts_after ->
    tseval s' (ts_before ++ c_n :: ts_after) s'' ->
    tseval s ts s''.
Hint Constructors tseval.

Fixpoint ts_reduce (ts:list thread) : thread :=
  nil.

Theorem tseval_to_seqeval:
  forall s ts s',
    tseval s ts s' <->
    tseval s ((ts_reduce ts)::nil) s'.
Proof.
Admitted.
