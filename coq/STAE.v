Inductive val : Set :=
| val_Bool : bool -> val
| val_Num : nat -> val .
Hint Constructors val.

Inductive term : Set :=
| term_Val : val -> term
| term_If : term -> term -> term -> term
| term_Add : term -> term -> term
| term_Not : term -> term 
| term_IsZero : term -> term.
Hint Constructors term.

Require Export Zerob.

Inductive HasVal : term -> val -> Prop :=
| HV_Val :
forall (v:val),
 HasVal (term_Val v) v
| HV_If_True :
forall (t1 t2 t3:term) (v:val),
 HasVal t1 (val_Bool true) ->
 HasVal t2 v ->
 HasVal (term_If t1 t2 t3) v
| HV_If_False :
forall (t1 t2 t3:term) (v:val),
 HasVal t1 (val_Bool false) ->
 HasVal t3 v ->
 HasVal (term_If t1 t2 t3) v
| HV_Add :
forall (t1 t2:term) (n1 n2:nat),
 HasVal t1 (val_Num n1) ->
 HasVal t2 (val_Num n2) ->
 HasVal (term_Add t1 t2) (val_Num (n1 + n2))
| HV_Not :
forall (t1:term) (b:bool),
 HasVal t1 (val_Bool b) ->
 HasVal (term_Not t1) (val_Bool (negb b))
| HV_IsZero :
forall (t1:term) (n:nat),
 HasVal t1 (val_Num n) ->
 HasVal (term_IsZero t1) (val_Bool (zerob n)).
Hint Constructors HasVal.

Lemma val_uniq :
 forall (t:term) (v1 v2:val),
  HasVal t v1 ->
  HasVal t v2 ->
  v1 = v2.
Proof.
 intros t. induction t; intros v1 v2;
  intros Hv1; inversion_clear Hv1; 
  intros Hv2; inversion_clear Hv2; eauto.

 eapply IHt2; eauto.
 Ltac val_uniq_kill := 
  absurd ( val_Bool true = val_Bool false ); eauto;
  intros X; inversion X.
 val_uniq_kill. val_uniq_kill.

 Ltac val_uniq_skill val_Num n1 n0 :=
  assert (n1 = n0) as Veq; 
   [ assert ((val_Num n1) = (val_Num n0)) as val_eq; eauto; 
     inversion_clear val_eq; eauto
   | rewrite Veq; clear Veq; eauto ].

 val_uniq_skill val_Num n1 n0.
 val_uniq_skill val_Num n2 n3.
 val_uniq_skill val_Bool b b0.
 val_uniq_skill val_Num n n0.
Qed.
Hint Resolve val_uniq.

Theorem val_dec :
       forall t:term,
        { v:val | HasVal t v } + { forall v:val, ~ HasVal t v }.
Proof.
 intros t. induction t; eauto.

 Ltac ChooseFalse' :=
  right; intros v0 HV; inversion_clear HV; eauto.
 Ltac IH_Split' IH ty :=
  case IH; [ clear IH; intros IH; case IH; clear IH;
             intros ty; case ty; clear ty;
              [ intros ty; case ty; clear ty | intros ty ];
             intros IH
           | clear IH; intros IH; ChooseFalse'; eapply IH; eauto ].
 Ltac IH_Split'' IH ty :=
  case IH; [ clear IH; intros IH; case IH; clear IH;
             intros ty; case ty; clear ty;
              [ intros ty; case ty; clear ty | intros ty ];
             intros IH
           | clear IH; intros IH; ChooseFalse'; eauto ].
 Ltac BeAbsurd' lhs rhs :=
  absurd ( lhs = rhs); eauto; intros X; inversion X.

 IH_Split' IHt1 v1; eauto.

 IH_Split'' IHt2 v2; eauto.
 eapply IHt2; eauto.
 BeAbsurd' (val_Bool true) (val_Bool false).

 IH_Split'' IHt3 v3; eauto.
 BeAbsurd' (val_Bool true) (val_Bool false).
 eapply IHt3; eauto.

 ChooseFalse'.
 BeAbsurd' (val_Num v1) (val_Bool true).
 BeAbsurd' (val_Num v1) (val_Bool false).

 IH_Split' IHt1 v1; eauto.
  ChooseFalse'; BeAbsurd' (val_Num n1) (val_Bool true).
  ChooseFalse'; BeAbsurd' (val_Num n1) (val_Bool false).

 IH_Split' IHt2 v2; eauto.
  ChooseFalse'; BeAbsurd' (val_Num n2) (val_Bool true).
  ChooseFalse'; BeAbsurd' (val_Num n2) (val_Bool false).

 IH_Split' IHt v; eauto.
  ChooseFalse'; BeAbsurd' (val_Num v) (val_Bool b).

 IH_Split' IHt v; eauto.
  ChooseFalse'; BeAbsurd' (val_Num n) (val_Bool true).
  ChooseFalse'; BeAbsurd' (val_Num n) (val_Bool false).
Qed.

Inductive ty : Set :=
| ty_Bool : ty
| ty_Num : ty.
Hint Constructors ty.

Inductive HasType : term -> ty -> Prop :=
| HT_Val_Bool :
forall (b:bool),
 HasType (term_Val (val_Bool b)) ty_Bool
| HT_Val_Num :
forall (n:nat),
 HasType (term_Val (val_Num n)) ty_Num
| HT_If :
forall (t1 t2 t3:term) (T1:ty),
 HasType t1 ty_Bool ->
 HasType t2 T1 ->
 HasType t3 T1 ->
 HasType (term_If t1 t2 t3) T1
| HT_Add :
forall (t1 t2:term),
 HasType t1 ty_Num ->
 HasType t2 ty_Num ->
 HasType (term_Add t1 t2) ty_Num
| HT_Not :
forall (t1:term),
 HasType t1 ty_Bool ->
 HasType (term_Not t1) ty_Bool
| HT_IsZero :
forall (t1:term),
 HasType t1 ty_Num ->
 HasType (term_IsZero t1) ty_Bool.
Hint Constructors HasType.

Lemma ty_uniq :
 forall (t:term) (T1 T2:ty),
  HasType t T1 ->
  HasType t T2 ->
  T1 = T2.
Proof.
 intros t. induction t; intros T1 T2; [ case v; intros r | | | | ];
  intros HT1 HT2; inversion_clear HT1; inversion_clear HT2; eauto.
Qed.
Hint Resolve ty_uniq.

Theorem ty_dec :
       forall t:term,
        { T:ty | HasType t T } + { forall ty, ~ HasType t ty }.
Proof.
 intros t.
 induction t; eauto.
 (* val *)
 case v; eauto.
 (* if *)
 Ltac ChooseFalse :=
  right; intros ty0; intro HT; inversion_clear HT; eauto.
 Ltac IH_Split IH ty :=
  case IH; [ clear IH; intros IH; case IH; clear IH;
             intros ty; case ty; clear ty; intros IH
           | clear IH; intros IH; ChooseFalse; eapply IH; eauto ].
 Ltac BeAbsurd :=
  absurd (ty_Bool = ty_Num); eauto; intros H3; inversion H3.

 IH_Split IHt1 ty1; eauto.
 IH_Split IHt2 ty2; eauto.
 IH_Split IHt3 ty3; eauto.

 ChooseFalse.
 rewrite (ty_uniq t2 ty0 ty_Bool H0 IHt2) in H1.
 BeAbsurd.

 IH_Split IHt3 ty3; eauto.

 ChooseFalse.
 rewrite (ty_uniq t3 ty0 ty_Bool H1 IHt3) in H0.
 BeAbsurd.

 ChooseFalse. BeAbsurd.
 (* add *)
 IH_Split IHt1 ty1; eauto.
 IH_Split IHt2 ty2; eauto.

 ChooseFalse. BeAbsurd.
 ChooseFalse. BeAbsurd.
 IH_Split IHt2 ty2; eauto.
 ChooseFalse. BeAbsurd.
 (* not *)
 IH_Split IHt ty1; eauto.
 ChooseFalse. BeAbsurd.
 (* iszero *)
 IH_Split IHt ty1; eauto.
 ChooseFalse. BeAbsurd.
Qed.

Theorem soundness :
 forall (t0:term) (T0:ty) (v0:val),
   HasType t0 T0 ->
   HasVal t0 v0 ->
   HasType (term_Val v0) T0.
Proof.
 intros t0.

 induction t0; [ case v; intros vv | | | | ]; intros T0 v0 HT HV; 
  inversion_clear HT; inversion_clear HV; eauto.
Qed.

Lemma soundlike :
 forall (t0:term) (T0:ty),
  HasType t0 T0 ->
  exists v0:val,
   HasVal t0 v0.
Proof.
 intros t0.

 induction t0; [ case v; intros vv | | | | ]; intros T0 HT;
  inversion_clear HT; eauto.

 case (IHt0_1 ty_Bool H); eauto; intros v1; case v1.

 intros b; case b;
  intros HV1; eauto.
 case (IHt0_2 T0 H0); eauto.
 case (IHt0_3 T0 H1); eauto.
 
 (* XXX Make a tactic for these *)
 intros n HV1.
 generalize (soundness t0_1 ty_Bool (val_Num n) H HV1).
 intros HT. inversion_clear HT.

 case (IHt0_1 ty_Num H). intros v1; case v1; intros r1 HV1.
 generalize (soundness t0_1 ty_Num (val_Bool r1) H HV1).
 intros HT. inversion_clear HT.

 case (IHt0_2 ty_Num H0). intros v2; case v2; intros r2 HV2.
 generalize (soundness t0_2 ty_Num (val_Bool r2) H0 HV2).
 intros HT. inversion_clear HT.
 exists (val_Num (r1+r2)). eauto.

 case (IHt0 ty_Bool H). intros v0; case v0; intros r0 HV0; eauto.
 generalize (soundness t0 ty_Bool (val_Num r0) H HV0).
 intros HT. inversion_clear HT.

 case (IHt0 ty_Num H). intros v0; case v0; intros r0 HV0; eauto.
 generalize (soundness t0 ty_Num (val_Bool r0) H HV0).
 intros HT. inversion_clear HT.
Qed.

Theorem eval :
 forall (t0:term),
  { v0:val | HasVal t0 v0 } + { forall (T0:ty), ~ HasType t0 T0 }.
Proof.
 intros t0.

 case (val_dec t0);
  case (ty_dec t0);
   intros HT nHV; eauto.

 case HT. clear HT. intros T0 HT.
 right. intros T1 HT'.
 case (soundlike t0 T0); eauto.
Qed.

Extraction "STAE.ml" eval.