Require Import FMaps.

Module Nat2X := PositiveMap.

Inductive Mumthing : Set :=
  A : Mumthing
| B : Mumthing.

Definition NatMap := Nat2X.t Mumthing.

Definition odds : NatMap :=
 Nat2X.add 2 A
  (Nat2X.add 1 B (@Nat2X.empty Mumthing)).

Compute NatMap.

Inductive Something : Set :=
 C : NatMap -> Something.