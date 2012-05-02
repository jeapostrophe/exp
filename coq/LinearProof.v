Require Import "Linear".

Hypothesis b : atom.
Hypothesis a : atom.

Check
((P_Weak
  ((Atom b) :: nil)
  (gamma_single (Atom a))
  (Atom a)
  (P_Assume (Atom a)))
 :
 (Proves ((Atom a) :: ((Atom b) :: nil)) (Atom a)))
.
