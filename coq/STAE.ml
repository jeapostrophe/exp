type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type 'a sumor =
| Inleft of 'a
| Inright

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
  | O -> m
  | S p -> S (plus p m)

(** val zerob : nat -> bool **)

let zerob = function
| O -> True
| S n0 -> False

type val0 =
| Val_Bool of bool
| Val_Num of nat

type term =
| Term_Val of val0
| Term_If of term * term * term
| Term_Add of term * term
| Term_Not of term
| Term_IsZero of term

(** val val_dec : term -> val0 sumor **)

let rec val_dec = function
| Term_Val v -> Inleft v
| Term_If (t0, t1, t2) ->
  (match val_dec t0 with
   | Inleft iHt1 ->
     (match iHt1 with
      | Val_Bool v1 ->
        (match v1 with
         | True -> val_dec t1
         | False -> val_dec t2)
      | Val_Num v1 -> Inright)
   | Inright -> Inright)
| Term_Add (t0, t1) ->
  (match val_dec t0 with
   | Inleft iHt1 ->
     (match iHt1 with
      | Val_Bool v1 -> Inright
      | Val_Num v1 ->
        (match val_dec t1 with
         | Inleft iHt2 ->
           (match iHt2 with
            | Val_Bool v2 -> Inright
            | Val_Num v2 -> Inleft (Val_Num (plus v1 v2)))
         | Inright -> Inright))
   | Inright -> Inright)
| Term_Not t0 ->
  (match val_dec t0 with
   | Inleft iHt ->
     (match iHt with
      | Val_Bool v -> Inleft (Val_Bool (negb v))
      | Val_Num v -> Inright)
   | Inright -> Inright)
| Term_IsZero t0 ->
  (match val_dec t0 with
   | Inleft iHt ->
     (match iHt with
      | Val_Bool v -> Inright
      | Val_Num v -> Inleft (Val_Bool (zerob v)))
   | Inright -> Inright)

(** val eval : term -> val0 sumor **)

let eval t0 =
  val_dec t0

