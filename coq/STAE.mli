type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type 'a sumor =
| Inleft of 'a
| Inright

val plus : nat -> nat -> nat

val zerob : nat -> bool

type val0 =
| Val_Bool of bool
| Val_Num of nat

type term =
| Term_Val of val0
| Term_If of term * term * term
| Term_Add of term * term
| Term_Not of term
| Term_IsZero of term

val val_dec : term -> val0 sumor

type ty =
| Ty_Bool
| Ty_Num

val ty_dec : term -> ty sumor

val eval : term -> val0 sumor

