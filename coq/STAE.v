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
 Ltac DefFalse :=
  right; intros ty0; intro HT; inversion_clear HT; eauto.
 Ltac IH_Split IH ty :=
  case IH; [ clear IH; intros IH; case IH; clear IH;
             intros ty; case ty; clear ty; intros IH
           | clear IH; intros IH; DefFalse ].

 IH_Split IHt1 ty1; eauto.
 IH_Split IHt2 ty2; eauto.
 IH_Split IHt3 ty3; eauto.

 DefFalse. rewrite (ty_uniq t2 ty0 ty_Bool H0 IHt2) in *.
 absurd (ty_Bool = ty_Num); eauto. intros H3. inversion H3.

 IH_Split IHt3 ty3; eauto.

 right; intros ty0; intro HT; inversion_clear HT; eauto.
 rewrite (ty_uniq t3 ty0 ty_Bool H1 IHt3) in *.
 absurd (ty_Bool = ty_Num); eauto. intros H3. inversion H3.

 right; intros ty0; intro HT; inversion_clear HT; eauto.
 absurd (ty_Bool = ty_Num); eauto. intros H3. inversion H3.
 
 

Theorem eval :
       forall t:term, T:ty,
        HasType t ty ->
        { v | HasVal t v /\ HasType (Val v) ty } .

