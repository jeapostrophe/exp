Require Export List Permutation.
Open Scope list_scope.

Variable atom : Set.
Hypothesis atom_eq_dec : forall (x y:atom),
 { x = y } + { x <> y }.
Hint Resolve atom_eq_dec.

Inductive prop : Set :=
| Atom : atom -> prop
| Implies : prop -> prop -> prop.
Hint Constructors prop.

Theorem prop_eq_dec:
 forall (x y:prop), { x = y } + { x <> y }.
Proof.
 decide equality.
Qed.
Hint Resolve prop_eq_dec.
 
Definition Gamma := list prop.
Definition empty_gamma : Gamma := nil.
Definition gamma_add (x:prop) (g:Gamma) := x :: g.
Definition gamma_union (g g':Gamma) := g ++ g'.
Definition gamma_single (x:prop) := gamma_add x empty_gamma.
Hint Unfold empty_gamma gamma_add gamma_union gamma_single.

Inductive Proves : Gamma -> prop -> Prop :=
| P_Weak :
  forall (g g':Gamma) (b:prop),
   Proves g' b ->
   Proves (gamma_union g g') b
| P_Exchange :
  forall (g g':Gamma) (a:prop),
   Permutation g g' ->
   Proves g a ->
   Proves g' a

| P_Assume :
  forall (p:prop),
   Proves (gamma_single p) p

| P_Implies_Elim :
  forall (g g':Gamma) (pa pb:prop),
   Proves g (Implies pa pb) ->
   Proves g' pa ->
   Proves (gamma_union g g') pb.
Hint Constructors Proves.
