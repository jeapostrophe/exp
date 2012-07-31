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

Definition fahrenheitToCelsius (f:R) :=
 ((f - 32) * 5 / 9)%R.

Theorem a2_e2_e1:
 fahrenheitToCelsius (32)%R = (0)%R.
Proof.
 unfold fahrenheitToCelsius.
 field.
Qed.

Theorem a2_e2_e2:
 fahrenheitToCelsius (212)%R = (100)%R.
Proof.
 unfold fahrenheitToCelsius.
 field.
Qed.

(** Exercise 3 **)

Definition convert3 (x:nat) (y:nat) (z:nat) :=
 x + 10 * y + 100 * z.

Theorem a2_e3_e1:
 convert3 1 2 3 = 321.
Proof.
 tauto.
Qed.

Theorem a2_e3_e2:
 convert3 3 5 1 = 153.
Proof.
 tauto.
Qed.

(** Exercise 4 **)

Definition a2_e4 (n:nat) := n*n + 10.

Theorem a2_e4_e1:
 a2_e4 2 = 14.
Proof.
 tauto.
Qed.

Theorem a2_e4_e2:
 a2_e4 9 = 91.
Proof.
 tauto.
Qed.

(** Exercise 5 **)

Definition sum_coins p n d q :=
 p + (n*5) + (d*10) + (q*25).

Theorem a2_e5_e1:
 sum_coins 1 0 0 0 = 1.
Proof.
 tauto.
Qed.

Theorem a2_e5_e2:
 sum_coins 0 1 0 0 = 5.
Proof.
 tauto.
Qed.

Theorem a2_e5_e3:
 sum_coins 0 0 1 0 = 10.
Proof.
 tauto.
Qed.

Theorem a2_e5_e4:
 sum_coins 0 0 0 1 = 25.
Proof.
 tauto.
Qed.

Theorem a2_e5_e5:
 sum_coins 1 1 1 1 = 41.
Proof.
 tauto.
Qed.

(** Exercise 6 **)

Definition total_profit attendees :=
 ((attendees * 5) - (20 + (attendees / 2)))%R.

Theorem a2_e6_e1:
 total_profit 10%R = 25%R.
Proof.
 unfold total_profit.
 field.
Qed.

(** Exercise 7 **)

Definition dollarToYen d :=
 (d * 796 / 10)%R.

Theorem a2_e7_e1:
 dollarToYen 25 = 1990%R.
Proof.
 unfold dollarToYen. field.
Qed.

(** Exercise 8 **)

Definition areaOfTriangle base height :=
 (base * height * 1/2)%R.

Theorem a2_e8_e1:
 (areaOfTriangle 1 2 = 1)%R.
Proof.
 compute. field.
Qed.

(** Exercise 9 **)

Definition a2_e9 n :=
 ((1/2 * (n * n)) + 20)%R.

Theorem a2_e9_e1:
 (a2_e9 2 = 22)%R.
Proof.
 compute. field.
Qed.

Theorem a2_e9_e2:
 (a2_e9 9 = (60 + 1/2))%R.
Proof.
 compute. field.
Qed.

(* Assignment 3 *)

(** Exercise 1 **)
Inductive Sign : Set :=
| Positive : Sign
| Zero : Sign
| Negative : Sign.
Hint Constructors Sign.

Inductive SignOf : Z -> Sign -> Prop :=
| Is_Positive :
  forall z:Z, (z > 0)%Z -> SignOf z Positive
| Is_Zero :
  forall z:Z, (z = 0)%Z -> SignOf z Zero
| Is_Negative :
  forall z:Z, (z < 0)%Z -> SignOf z Negative.
Hint Constructors SignOf.

Theorem a3_e1:
forall z,
 { s | SignOf z s }.
Proof.
 intros z.
 destruct (Z_dec z 0) as [ [H | H] | H ]; eauto.
Qed.

Example a3_e1_e1:
 (SignOf (-2)%Z Negative).
Proof.
 cut ((-2 < 0)%Z); eauto.
 omega.
Qed.

(** Exercise 2 **)

Definition areaOfCircle radius :=
 (PI * radius * radius)%R.

Definition areaOfCylinder radius len :=
 ((areaOfCircle radius) * len)%R.

Definition areaOfTube inner len thickness :=
 ((areaOfCylinder (inner + thickness)%R len) 
  - (areaOfCylinder inner len))%R.

Example a3_e2_e1:
 areaOfTube 1%R 2%R 3%R = (30 * PI)%R.
Proof.
 unfold areaOfTube. unfold areaOfCylinder. unfold areaOfCircle.
 field.
Qed.

(** Exercise 3 **)

Definition a3_e3_speed t :=
 (2 * t)%R.

Definition a3_e3_height t :=
 (1/2 * (a3_e3_speed t) * t)%R.

Example a3_e3_e1:
 a3_e3_height 1%R = 1%R.
Proof.
 unfold a3_e3_height. unfold a3_e3_speed.
 field.
Qed.

(** Exercise 4 **)

Definition celsiusToFahrenheit (c:R) :=
 ((c / (5/9)) + 32)%R.

Theorem a3_e4_e1:
 celsiusToFahrenheit (0)%R = (32)%R.
Proof.
 unfold celsiusToFahrenheit.
 field.
Qed.

Theorem a3_e4_e2:
 celsiusToFahrenheit (100)%R = (212)%R.
Proof.
 unfold celsiusToFahrenheit.
 field.
Qed.

Theorem a3_e4_1:
 forall r, celsiusToFahrenheit ( fahrenheitToCelsius ( r ) ) = r.
Proof.
 intros r. 
 unfold fahrenheitToCelsius.
 unfold celsiusToFahrenheit.
 field.
Qed.

Theorem a3_e4_2:
 forall r,  fahrenheitToCelsius ( celsiusToFahrenheit ( r ) ) = r.
Proof.
 intros r. 
 unfold fahrenheitToCelsius.
 unfold celsiusToFahrenheit.
 field.
Qed.

(** Exercise 5 **)

(****** See above *)

(** Exercise 6 **)

Definition milesToFeet (m:R) :=
 (m * 5280)%R.

Theorem a3_e6_e1:
 milesToFeet (1)%R = (5280)%R.
Proof.
 unfold milesToFeet.
 field.
Qed.

Theorem a3_e6_e2:
 milesToFeet (6)%R = (31680)%R.
Proof.
 unfold milesToFeet.
 field.
Qed.

(* Assignment 4 *)
