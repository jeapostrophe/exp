Inductive Month : Set :=
| May : Month
| June : Month
| July : Month
| August : Month.
Hint Constructors Month.

Inductive Day : Set :=
| D_14 : Day
| D_15 : Day
| D_16 : Day
| D_17 : Day
| D_18 : Day
| D_19 : Day.
Hint Constructors Day.

Theorem Month_dec:
  forall (x y:Month), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Theorem Day_dec:
  forall (x y:Day), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Require Import List.

Definition options : list (Month * Day) :=
  (May, D_15) ::  (May, D_16) :: (May, D_19) ::
  (June, D_17) :: (June, D_18) ::
  (July, D_14) :: (July, D_16) ::
  (August, D_14) :: (August, D_15) :: (August, D_17) :: nil.

Definition is_month (m:Month) (x:Month * Day) : bool :=
  if Month_dec m (fst x) then true else false.

Definition is_day (d:Day) (x:Month * Day) : bool :=
  if Day_dec d (snd x) then true else false.

(* Cheryl's list of options includes her real birthday *)

Definition ValidDate (m:Month) (d:Day) :=
  In (m,d) options.

Ltac invalid_date VD :=
  (contradict VD; unfold ValidDate;
      simpl In; intros IN; intuition; congruence).

(* Albert doesn't know the date from the month alone *)

Definition AlbertInitial (m:Month) (d:Day) :=
  (length (filter (is_month m) options)) <> 1.

(* Albert's knowledge is weaker than ValidDate because anything
   provable with AI is provable with VD. *)

Lemma AlbertUseless:
  forall m d P,
    (ValidDate m d /\ AlbertInitial m d -> P)
    -> (ValidDate m d -> P).
Proof.
  intros m d P A.
  intros VD.
  apply A. split. auto.
  unfold AlbertInitial.
  clear A VD P d.
  destruct m; simpl filter; simpl length; auto.
Qed.

(* Albert knows that Bernard doesn't know the date from the day alone,
   because he knows that the day occurs in two months (i.e. occurs
   more than once overall) *)

Definition AlbertVersusBernard (m:Month) (d:Day) :=
  (forall m' d',
    In (m',d') (filter (is_month m) options) ->
    (count_occ Day_dec (@map (Month*Day) Day (@snd Month Day) options) d') > 1).

(* Thus, it can't be May or June because the 19th and 18th occur only
   in those months. So it must be July or August. *)

Lemma AlbertVersusBernard_discards_MayJune:
  forall m d,
    AlbertVersusBernard m d ->
    m = July \/ m = August.
Proof.
  intros m d AVB.
  destruct m; auto.

  assert False; try contradiction.
  remember (AVB May D_19) as AVB'.
  simpl count_occ in AVB'.
  assert (~ 1 > 1).
   intros H. inversion H. inversion H1.
  apply H. apply AVB'.
  apply in_cons. 
  apply in_cons.
  apply in_eq.

  assert False; try contradiction.
  remember (AVB June D_18) as AVB'.
  simpl count_occ in AVB'.
  assert (~ 1 > 1).
   intros H. inversion H. inversion H1.
  apply H. apply AVB'.
  apply in_cons. 
  apply in_eq.
Qed.

(* But now Bernard knows, i.e. the same day does not occur in both of
   the two remaining months of the options *)

Definition BernardKnows (m:Month) (d:Day) :=
  forall m1 m2,
    m = m1 \/ m = m2 ->
    ~ (In (m1, d) options /\ In (m2, d) options).

(* This implies that the day is not D_14 *)

Lemma BernardKnows_discards_14 :
  forall m d,
    ValidDate m d ->
    m = July \/ m = August ->
    BernardKnows m d ->
    d = D_15 \/ d = D_16 \/ d = D_17.
Proof.
  intros m d VD AVB BK.
  remember AVB as BK'. clear HeqBK'.
  apply BK in BK'. clear BK.

  destruct AVB; subst m;
    destruct d;
      try (invalid_date VD).

  contradict BK'.
  simpl In. split; intuition.

  auto.

  contradict BK'.
  simpl In. split; intuition.
  
  auto.
  
  auto.
Qed.

(* But now Albert knows which means that the month he was told (the
   real month) doesn't have more than one of the available dates,
   because otherwise he wouldn't be able to know *)

Definition AlbertKnows (m:Month) (d:Day) :=
  forall d1 d2 d3,
    d = d1 \/ d = d2 \/ d = d3 ->
    (* Only d3 is there *) ~ (In (m,d1) options /\ In (m,d2) options) /\
    (* Only d1 is there *) ~ (In (m,d2) options /\ In (m,d3) options) /\
    (* Only d2 is there *) ~ (In (m,d3) options /\ In (m,d1) options).

Lemma AlbertKnows_discards_August :
  forall m d,
    ValidDate m d ->
    m = July \/ m = August ->
    d = D_15 \/ d = D_16 \/ d = D_17 ->
    AlbertKnows m d ->
    m = July.
Proof.
  intros m d VD AVB BKR AK.
  remember BKR as AK'. clear HeqAK'.
  apply AK in AK'. clear AK.
  destruct AK' as [AK'1 [AK'2 AK'3]].

  destruct AVB; subst m.
  auto.
  
  destruct BKR as [BKR | [BKR | BKR]]; subst d.

  contradict AK'3. simpl In. split; intuition.

  invalid_date VD.
  
  contradict AK'3. simpl In. split; intuition.
Qed.

Theorem Problem:
  forall m d,
    (* The real date is one that she told us *)
    ValidDate m d ->
    (* Albert was told m, but his set is not empty *) 
    AlbertInitial m d ->
    (* Albert knows that month m doesn't have a non-duplicated date,
       ergo Bernard doesn't know the answer *)
    AlbertVersusBernard m d ->
    (* Now that Bernard knows that May and June aren't it, Bernard
       knows the answer, this means he wasn't told the 14th because
       that is shared on July and August and if the answer was shared,
       then he'd be toast *)
    BernardKnows m d ->
    (* Now Albert can figure out that it was the 15, 16, or 17, but he
       knows the month, so now he knows *)
    AlbertKnows m d ->
    (* Thus the only day is July 16th. *)
    ((m = July) /\ d = D_16).
Proof.
  intros m d VD AI AVB BK AK.
  clear AI.
  apply AlbertVersusBernard_discards_MayJune in AVB.
  apply BernardKnows_discards_14 in BK; auto.
  apply AlbertKnows_discards_August in AK; auto.

  subst m.
  destruct BK as [BK | [BK | BK]]; subst;
    try (invalid_date VD).

  auto.
Qed.
