Require Import "Linear".

Hypothesis radio : atom.
Hypothesis car : atom.
Hypothesis part112 : atom.

Check
((P_Exchange
  (gamma_union
   (gamma_single (Implies (Atom radio) (Atom car)))
   (gamma_union
    (gamma_single (Implies (Atom part112) (Atom radio)))
    (gamma_single (Atom part112))))
  ((Implies (Atom part112) (Atom radio))
   ::
   ((Atom part112) :: ((Implies (Atom radio) (Atom car)) :: nil)))
  (Atom car)
  (@Permutation_cons_app
   prop
   ((Implies (Atom part112) (Atom radio)) :: ((Atom part112) :: nil))
   ((Implies (Atom part112) (Atom radio)) :: ((Atom part112) :: nil))
   nil
   (Implies (Atom radio) (Atom car))
   (perm_skip
    (Implies (Atom part112) (Atom radio))
    (perm_skip (Atom part112) (perm_nil prop))))
  (P_Implies_Elim
   (gamma_single (Implies (Atom radio) (Atom car)))
   (gamma_union
    (gamma_single (Implies (Atom part112) (Atom radio)))
    (gamma_single (Atom part112)))
   (Atom radio)
   (Atom car)
   (P_Assume (Implies (Atom radio) (Atom car)))
   (P_Implies_Elim
    (gamma_single (Implies (Atom part112) (Atom radio)))
    (gamma_single (Atom part112))
    (Atom part112)
    (Atom radio)
    (P_Assume (Implies (Atom part112) (Atom radio)))
    (P_Assume (Atom part112)))))
 :
 (Proves
  ((Implies (Atom part112) (Atom radio))
   ::
   ((Atom part112) :: ((Implies (Atom radio) (Atom car)) :: nil)))
  (Atom car)))
.
