Require Import Reals.
Require Import Psatz.

Local Open Scope R_scope.

Definition theta (f:R -> R) (g:R -> R) :=
  exists (c_1 c_2 n_0:R),
       c_1 > 0 /\
       c_2 > 0 /\
       n_0 > 0 /\ 
       (forall (n:R),
         n >= n_0 ->
         0 <= c_1 * g n /\
         c_1 * g n <= f n /\ 
         f n <= c_2 * g n).

Lemma Rpower_gt0:
  forall x y,
    Rpower x y > 0.
Proof.
  intros x y.
  Print Rlt_gt.
  eapply Rlt_gt.
  unfold Rpower.
  apply exp_pos.
Qed.

Lemma Rpower_mult_mult:
  forall x y z,
    0 < x ->
    0 < y -> 
    Rpower x z * Rpower y z = Rpower (x * y) z.
Proof.
  intros x y z lt_x lt_y.
  unfold Rpower.
  rewrite <- exp_plus.
  rewrite <- Rmult_plus_distr_l.
  rewrite ln_mult; auto.
Qed.

Theorem Pr_3p1_2:
  forall (a b:R),
    b > 0 ->
    theta 
    (fun (n:R) => Rpower (n + a) b)
    (fun (n:R) => Rpower n b).
Proof.
 intros A B Bpos.
 unfold theta.
 
 exists (Rpower (1/2) B).
 exists (Rpower (3/2) B).
 exists (2 * Rabs A + 1).
 
 (* 1/2^B is positive *)
 split. apply Rpower_gt0.

 (* 3/2^B is positive *)
 split. apply Rpower_gt0.

 (* 2|A| + 1 > 0 *)
 split.
 eapply Rlt_gt.
 apply Rle_lt_0_plus_1. 
 replace (2 * Rabs A) with (Rabs A + Rabs A).
 eapply Rle_trans.
 apply Rabs_pos.
 apply Rabs_triang.
 field.
 
 (* Ineqs *)
 intros N Nge.

 split; [idtac | split].

 assert (N > 0) as Npos.
 apply Rlt_gt.
 apply Rge_le in Nge.
 destruct Nge as [Ngt | Neq].
 eapply Rlt_trans; [ idtac | apply Ngt ].
 apply Rle_lt_0_plus_1.
 eapply Rle_trans.
 apply Rabs_pos.

 replace 0 with (0 * 0); [idtac | field].
 apply Rmult_le_compat.
 apply Rle_refl.
 apply Rle_refl.
 lra.

 SearchAbout Rlt 0.
 unfold Rle in Nge.

 (* pos *)
 apply Rle_refl.
 apply Rle_refl.

 unfold Rle. left. unfold Rpower. apply exp_pos.
 unfold Rle. left. unfold Rpower. apply exp_pos.

 (* left *)
 rewrite Rpower_mult_mult.

 replace (Rpower (1 / 2) B * Rpower N B) with
         (Rpower ((1/2)*N) B).
 
