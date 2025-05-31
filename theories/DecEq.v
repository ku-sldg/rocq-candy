(*
Generic Typeclass for equality, plus some instances.

Authors:  Adam Petz, ampetz@ku.edu
          Will Thomas, 30wthomas@ku.edu
 *)

From Stdlib Require Import Setoid String List Decidable.
From RocqCandy Require Import Tactics.

Class DecEq (A : Type) := {
  dec_eq : forall x y : A, {x = y} + {x <> y}
}.

