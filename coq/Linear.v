Require Import List Permutation.
Local Open Scope list_scope.

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
  forall (g:Gamma) (a b:prop),
   Proves g b ->
   Proves (gamma_add a g) b
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

Require Import Coq.Program.Equality.
Lemma Proves_nil :
 forall (p:prop),
  ~ Proves empty_gamma p.
Proof.
 intros p P. dependent induction P; eauto.

 eapply IHP; eapply Permutation_nil; eapply Permutation_sym; auto.

 apply app_eq_nil in x; destruct x; auto.
Qed.
Hint Resolve Proves_nil.

Lemma Proves_Weak_app :
 forall (gb g ga:Gamma) (p:prop),
  Proves g p ->
  Proves (gb ++ g ++ ga) p.
Proof.
Admitted.
Hint Resolve Proves_Weak_app.

Fixpoint list_splits (A:Type) (l:list A) :=
 match l with
  | nil =>
    (nil,nil)::nil
  | x :: l =>
    (nil, x :: l) ::
    (map (fun lhs_x_rhs:(list A * list A) =>
           let (lhs,rhs) := lhs_x_rhs in
           (x::lhs,rhs))
         (list_splits A l))
 end.

Theorem list_splits_correct :
 forall (A:Type) (l:list A),
  forall (lhs rhs:list A),
   In (lhs,rhs) (list_splits A l)
   <->
   l = lhs ++ rhs.
Proof.
 intros A l lhs rhs.
 induction l as [ | a l ]; simpl.


Theorem list_splits :
 forall (A:Type) (l:list A),
  { splits : list (list A * list A) |
    forall (lhs rhs:list A),
     In (lhs,rhs) splits <->
     l = lhs ++ rhs }.
Proof.
 intros A l.

 induction l as [ | a l ].
 
 exists ((nil,nil)::nil). intros lhs rhs. split.
 intros IN. eapply in_inv in IN.
 destruct IN as [IN|IN]; inversion IN; auto.

 intros EQ. symmetry in EQ. apply app_eq_nil in EQ.
 destruct EQ. rewrite H. rewrite H0. eapply in_eq.

 destruct IHl as [ splits IHl ].

 exists ((nil,a::l)::(map (fun lhs_x_rhs =>
          match lhs_x_rhs with
           | (lhs, rhs) =>
             ((a::lhs),rhs)
          end) splits)).
 intros lhs rhs. split; [ intros IN | intros EQ ].

 apply in_inv in IN.
 destruct IN as [ IN | IN ].
 inversion IN. simpl. auto.
 
 apply in_map_iff in IN.
 destruct IN as [ lhs_x_rhs IN ].
 destruct lhs_x_rhs as [ lhs_l rhs_l ].
 destruct IN as [ EQ IN ].
 rewrite IHl in IN. rewrite IN.
 inversion EQ. simpl. auto. 

 destruct lhs as [|x lhs]; simpl in EQ.

 rewrite EQ. apply in_eq.

 inversion EQ.
 rewrite <- IHl in H1.
 apply in_cons. apply in_map_iff.
 exists (lhs,rhs). auto.
Qed.

Theorem list_ind_split :
 forall (A:Type) (P:list A -> list A -> Prop),
  (forall (lhs rhs:list A), { P lhs rhs } + { ~ P lhs rhs }) ->
  forall (l:list A),
   { lhs_x_rhs:(list A * list A) |
     let (lhs,rhs) := lhs_x_rhs in l = lhs ++ rhs /\ P lhs rhs }
   + { forall (lhs rhs:list A), l = lhs ++ rhs -> ~ P lhs rhs }.
Proof.
 intros A P P_dec l.

 destruct (list_splits A l) as [ls lsP].
 
 induction ls.

 right. intros lhs rhs. rewrite <- lsP. intros IN.
 inversion IN.

 destruct a as [lhs rhs].
 case (P_dec lhs rhs) as [Pa | NPa].
 left. exists (lhs,rhs). rewrite <- lsP. split.
 eapply in_eq. auto.

 case (IHls).

 intros lhs' rhs'. rewrite <- lsP. 
 split; intros IN.
 eapply in_cons. auto.
 apply in_inv in IN. destruct IN as [EQ|IN].
 inversion EQ. rewrite H0 in *. rewrite H1 in *.
 clear EQ lhs rhs H0 H1.
 rewrite lsP.


  (exists (lhs rhs:list A), P (lhs ++ rhs))  

  P nil ->
  (forall (l l':list A), P l -> P l' -> P (l ++ l')) ->
  forall l : list A, P l.
Proof.
 intros A P Pnil Psplit l.

 destruct (list_splits A l) as [ ls lsP ].

 generalize lsP. clear lsP.
 case l; clear l.
 auto.
 intros a l lsP.

 destruct ls.
 absurd (a :: l = nil). discriminate.
 rewrite lsP.

 apply 
 
 induction (list_splits l).

fun (A : Type) (P : list A -> Prop) => list_rect P
     : forall (A : Type) (P : list A -> Prop),
       P nil ->
       (forall (a : A) (l : list A), P l -> P (a :: l)) ->
       forall l : list A, P l


Theorem Proves_dec:
 forall (g:Gamma) (p:prop),
  { Proves g p } + { ~ Proves g p }.
Proof.
 (* XXX New idea: Consider every permutation and splitting of g *)


 (* We go by induction on the size of the assumption environment. *)
 induction g as [ | gp g ]; intros p.

 (* The empty env can't prove anything. WRONG!! *)
 right. eauto.

 (* Next, we see if the smaller env can prove the prop. *)
 case (IHg p) as [ P | NP ].

 (* If it can, then the proof is easy. *)
 left. eapply P_Weak. eauto.

 (* Given that it can't that means that 'gp' is so how essential in the proof. *)

 (* Is it trivially essential? *)
 case (prop_eq_dec gp p) as [ EQ | NEQ ]. subst.
 left. eapply (Proves_Weak_app nil (p::nil) g).
 eapply P_Assume.

 case (IHg (Implies gp p)) as [ PI | NPI ].

 left. assert (gp :: g = gamma_union (gamma_single gp) g).
 auto. rewrite H. clear H.
 eapply P_Exchange. eapply Permutation_app_comm.
 eapply P_Implies_Elim. eapply PI.
 eapply P_Assume.

 right. intros P.
 inversion P; auto.

 clear H2 H1 g' a.

 Focus 2.
 clear pb H2.
 
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
 rewrite EQ1. eapply P_Assume.
 case (prop_eq_dec gp p2) as [EQ2 | NEQ2].
 left. eapply P_Or_Intro_Right.
 eapply (Proves_Weak_app nil (gp::nil) g).
 rewrite EQ2. eapply P_Assume.
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
