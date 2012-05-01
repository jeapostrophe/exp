Require Import List.
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
Hint Unfold empty_gamma gamma_add gamma_union.

Inductive Proves : Gamma -> prop -> Gamma -> Prop :=
| P_Atom_Intro :
  forall (g:Gamma) (p:prop),
   Proves (gamma_add p g) p g

| P_Or_Intro_Left :
  forall (g d:Gamma) (pa pb:prop),
   Proves (gamma_union g d) pa d ->
   Proves (gamma_union g d) (Or pa pb) d
| P_Or_Intro_Right :
  forall (g d:Gamma) (pa pb:prop),
   Proves (gamma_union g d) pb d ->
   Proves (gamma_union g d) (Or pa pb) d
| P_Or_Elim :
  forall (g g' g'':Gamma) (pa pb pc:prop),
   Proves (gamma_union g (gamma_union g' g'')) (Or pa pb) (gamma_union g' g'') ->
   Proves (gamma_add pa (gamma_union g' g'')) pc g'' ->
   Proves (gamma_add pb (gamma_union g' g'')) pc g'' ->
   Proves (gamma_union g (gamma_union g' g'')) pc g''

| P_And_Intro :
  forall (g g' g'':Gamma) (pa pb:prop),
   Proves (gamma_union g (gamma_union g' g'')) pa (gamma_union g' g'') ->
   Proves (gamma_union g' g'') pb g'' ->
   Proves (gamma_union g (gamma_union g' g'')) (And pa pb) g''
| P_And_Elim :
  forall (g g' g'':Gamma) (pa pb pc:prop),
   Proves (gamma_union g (gamma_union g' g'')) (And pa pb) (gamma_union g' g'') ->
   Proves (gamma_add pa (gamma_add pb (gamma_union g' g''))) pc g'' ->
   Proves (gamma_union g (gamma_union g' g'')) pc g''

| P_Implies_Intro :
  forall (g g':Gamma) (pa pb:prop),
   Proves (gamma_add pa (gamma_union g g')) pb g' ->
   Proves (gamma_union g g') (Implies pa pb) g'
| P_Implies_Elim :
  forall (g g' g'':Gamma) (pa pb:prop),
   Proves (gamma_union g (gamma_union g' g'')) (Implies pa pb) (gamma_union g' g'') ->
   Proves (gamma_union g' g'') pa g'' ->
   Proves (gamma_union g (gamma_union g' g'')) pb g''.
Hint Constructors Proves.

Lemma Proves_nil :
 forall (p:prop) (g':Gamma),
  ~ Proves empty_gamma p g'.
Proof.
Admitted.
Hint Resolve Proves_nil.

Lemma Proves_weaken:
 forall (g g' d:Gamma) (p:prop),
  Proves g p g' ->
  Proves (gamma_union d g) p (gamma_union d g').
Proof.
Admitted.
Hint Resolve Proves_weaken.

Lemma Proves_weaken_add:
 forall (g g':Gamma) (p d:prop),
  Proves g p g' ->
  Proves (gamma_add d g) p (gamma_add d g').
Proof.
 intros g g' p d P.
 generalize (Proves_weaken g g' (gamma_add d empty_gamma) p P).
 eauto.
Qed.
Hint Resolve Proves_weaken_add.

Theorem Proves_dec:
 forall (g:Gamma) (p:prop),
  { g' : Gamma | Proves g p g' } + { forall (g':Gamma), ~ Proves g p g' }.
Proof.
 (* We go by induction on the size of the assumption environment. *)
 induction g as [ | gp g ]; intros p.

 (* The empty env can't prove anything. *)
 right. eauto.

 (* Next, we see if the smaller env can prove the prop. *)
 case (IHg p) as [ [g' P] | NP ].

 (* If it can, then the proof is easy. *)
 left. exists (gamma_add gp g'). eapply Proves_weaken_add. auto.

 (* Given that it can't that means that 'gp' is so how essential in the proof. *)

 (* Is it trivially essential? *)
 case (prop_eq_dec gp p) as [ EQ | NEQ ]. subst.
 left. exists g. eapply P_Atom_Intro.

 (* Now we know it is essential (or the prop is false) but we're not sure how. *)
 
 (* We'll do induction on p because then we'll know to use the introduction forms. *)
 case p.

 Focus 2. (* The or case *)
 intros p0 p1. case (IHg p1) as [ [g' P1] | NP1 ].
 left. exists (gamma_add gp (gamma_union empty_gamma g')).
 eapply Proves_weaken_add.
 assert (g = (gamma_union empty_gamma g)) as EQ. auto.
 rewrite EQ. 

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
