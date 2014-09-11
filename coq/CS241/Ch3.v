Require Import Reals.

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
 exists (2 * Rabs A).
 split.
 
 (* 1/2^B is positive *)
 eapply Rlt_gt.
 unfold Rpower.


 eapply Rpower_lt.
