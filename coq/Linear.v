Require Import List Permutation.
Local Open Scope list_scope.

Variable atom : Set.
Hypothesis atom_eq_dec : forall (x y:atom), { x = y } + { x <> y }.
Hint Resolve atom_eq_dec.

Inductive prop : Set :=
| Atom : atom -> prop
| Or : prop -> prop -> prop
| And : prop -> prop -> prop
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
  forall (g:Gamma) (a b:prop),
   Proves g b ->
   Proves (gamma_add a g) b
| P_Exchange :
  forall (g g':Gamma) (a:prop),
   Permutation g g' ->
   Proves g a ->
   Proves g' a

| P_Atom_Intro :
  forall (p:prop),
   Proves (gamma_single p) p

| P_Or_Intro_Left :
  forall (g:Gamma) (pa pb:prop),
   Proves g pa ->
   Proves g (Or pa pb)
| P_Or_Intro_Right :
  forall (g:Gamma) (pa pb:prop),
   Proves g pb ->
   Proves g (Or pa pb)
| P_Or_Elim :
  forall (g g' g'':Gamma) (pa pb pc:prop),
   Proves g (Or pa pb) ->
   Proves (gamma_add pa g') pc ->
   Proves (gamma_add pb g'') pc ->
   Proves (gamma_union g (gamma_union g' g'')) pc

| P_And_Intro :
  forall (g g':Gamma) (pa pb:prop),
   Proves g pa ->
   Proves g' pb ->
   Proves (gamma_union g g') (And pa pb)
| P_And_Elim :
  forall (g g' g'':Gamma) (pa pb pc:prop),
   Proves g (And pa pb) ->
   Proves (gamma_add pa (gamma_add pb g')) pc ->
   Proves (gamma_union g g') pc

| P_Implies_Intro :
  forall (g:Gamma) (pa pb:prop),
   Proves (gamma_add pa g) pb ->
   Proves g (Implies pa pb)
| P_Implies_Elim :
  forall (g g':Gamma) (pa pb:prop),
   Proves g (Implies pa pb) ->
   Proves g' pa ->
   Proves (gamma_union g g') pb.
Hint Constructors Proves.

Lemma Proves_nil :
 forall (p:prop),
  ~ Proves empty_gamma p.
Proof.
 intros p P. induction P; eauto.


Admitted.
Hint Resolve Proves_nil.

Lemma Proves_Weak_app :
 forall (gb g ga:Gamma) (p:prop),
  Proves g p ->
  Proves (gb ++ g ++ ga) p.
Proof.
Admitted.
Hint Resolve Proves_Weak_app.

Theorem Proves_dec:
 forall (g:Gamma) (p:prop),
  { Proves g p } + { ~ Proves g p }.
Proof.
 intros g p. generalize g. induction p; eauto.



 (* We go by induction on the size of the assumption environment. *)
 induction g as [ | gp g ]; intros p.

 (* The empty env can't prove anything. *)
 right. eauto.

 (* Next, we see if the smaller env can prove the prop. *)
 case (IHg p) as [ P | NP ].

 (* If it can, then the proof is easy. *)
 left. eapply P_Weak. eauto.

 (* Given that it can't that means that 'gp' is so how essential in the proof. *)

 (* Is it trivially essential? *)
 case (prop_eq_dec gp p) as [ EQ | NEQ ]. subst.
 left. eapply (Proves_Weak_app nil (p::nil) g).
 eapply P_Atom_Intro.

 (* Now we know it is essential (or the prop is false) but we're not sure how. *)
 
 (* We'll do induction on p because then we'll know to use the introduction forms. *)
 induction p.

 Focus 2. (* The or case *)
 case (IHg p1) as [ P1 | NP1 ].
 left.
 eapply P_Weak. eapply P_Or_Intro_Left. auto.
 case (IHg p2) as [ P2 | NP2 ].
 left.
 eapply P_Weak. eapply P_Or_Intro_Right. auto.
 case (prop_eq_dec gp p1) as [EQ1 | NEQ1].
 left. eapply P_Or_Intro_Left.
 eapply (Proves_Weak_app nil (gp::nil) g).
 rewrite EQ1. eapply P_Atom_Intro.
 case (prop_eq_dec gp p2) as [EQ2 | NEQ2].
 left. eapply P_Or_Intro_Right.
 eapply (Proves_Weak_app nil (gp::nil) g).
 rewrite EQ2. eapply P_Atom_Intro.
 case (IHp1 NP1 NEQ1) as [IP1 | INP1].
 eauto.
 case (IHp2 NP2 NEQ2) as [IP2 | INP2].
 eauto.
 clear IHp1 IHp2.
 right. intros P. 

 inversion P; eauto.

 Focus 2.

 clear H1 H2 g' a. rename g0 into g'.
 generalize (P_Exchange g' (gp::g) (Or p1 p2) H H0).
 
 (* XXX We are primarily stuck because there's no relation between g and g' *)

eapply P_Or_Intro_Left.

 generalize (Proves_weaken_add g g' p gp P). auto.

 assert (gp :: g = gamma_union (gamma_add gp empty_gamma) g) as EQ. auto.
 rewrite EQ. eapply P_Or_Intro_Left.

 generalize (P_Or_Intro_Left (gamma_add gp empty_gamma) g p1 p2). simpl.

 right. intros g' P.
 inversion P; eauto.
 clear pc H3. rewrite H4 in *. clear g'' H4.
 rewrite H in *.


eapply NP. inversion P; eauto.
