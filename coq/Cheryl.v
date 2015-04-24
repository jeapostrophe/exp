Inductive Month : Set :=
| May : Month
| June : Month
| August : Month
| July : Month.
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
  (May, D_15) :: (May, D_16) :: (May, D_19) ::
  (June, D_17) :: (June, D_18) ::
  (July, D_14) :: (July, D_16) ::
  (August, D_14) :: (August, D_15) :: (August, D_17) :: nil.

Definition is_month (m:Month) (x:Month * Day) : bool :=
  if Month_dec m (fst x) then true else false.

Definition is_day (d:Day) (x:Month * Day) : bool :=
  if Day_dec d (snd x) then true else false.

Require Import Omega.

Theorem Problem:
  forall m d,
    (* Albert was told m, but his set is not empty *) 
    (length (filter (is_month m) options)) <> 1 ->
    (* Albert knows that month m doesn't have a non-duplicated date,
       ergo Bernard doesn't know the answer *)
    (forall m' d',
      In (m',d') (filter (is_month m) options) ->
      (count_occ Day_dec (@map (Month*Day) Day (@snd Month Day) options) d') > 1) ->
    (* Now that Bernard knows that, Bernard knows the answer *)
    (* Thus the only day is July 16th. *)
    ((m = July) /\ d = D_16).
Proof.
  intros m d. simpl map.
  destruct m; simpl filter; simpl length; intros A B.

  assert False; try contradiction.
  remember (B May D_19) as B'.
  simpl count_occ in B'.
  assert (~ 1 > 1). omega.
  apply H. apply B'.
  apply in_cons. 
  apply in_cons.
  apply in_eq.
  
  assert False; try contradiction.
  remember (B June D_18) as B'.
  simpl count_occ in B'.
  assert (~ 1 > 1). omega.
  apply H. apply B'.
  apply in_cons. 
  apply in_eq.

  assert False; try contradiction.
  remember (B June D_18) as B'.
  simpl count_occ in B'.
  assert (~ 1 > 1). omega.
  apply H. apply B'.
  apply in_cons. 
  apply in_eq.

  
  
