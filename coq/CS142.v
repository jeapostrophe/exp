Require Import Reals.

(* Assignment 1 *)

Theorem a1_e1:
 (( 12 / 8 ) * 3)%R = ( 4 + 1/2 )%R.
Proof.
 field.
Qed.

Theorem a1_e2:
 (((50 * 8) + (80 * 1)) / 9)%R = (53 + 1/3)%R.
Proof.
 field.
Qed.

(* Assignment 2 *)

(** Exercise 1 **)
Definition tip (price:R) := 
 (price * 15/100)%R.
Definition shareWithTip (pizza:R) (slices:R) (slices_sensible:(slices <= 8)%R) :=
 tip (pizza / 8 * slices)%R.

Theorem a2_e1_p1:
 forall (pizza:R) (slices:R) (slices_sensible:(slices <= 8)%R),
  (slices > 0)%R ->
  (100/15 * (shareWithTip pizza slices slices_sensible) / slices * 8 = pizza)%R.
Proof.
 unfold shareWithTip. unfold tip.
 intros pizza slices slices_sensible slices_pos.
 field.
 apply Rlt_dichotomy_converse. auto.
Qed.

Theorem a2_e1_p2:
 forall (pizza:R),
  {p | shareWithTip pizza (0)%R p = 0%R }.
Proof.
 intros pizza.
 cut (0 <= 8)%R. intros p.
 exists p.
 unfold shareWithTip. unfold tip.
 field. 
 apply Rlt_le.
 prove_sup.
Qed.

Theorem a2_e1_e1:
  {p | shareWithTip 12%R 3%R p = tip ( 4 + 1/2 )%R }.
Proof.
 cut (3 <= 8)%R. intros p. exists p.
 unfold shareWithTip. unfold tip.
 field.
 apply Rlt_le. prove_sup.
Qed.

(** Exercise 2 **)