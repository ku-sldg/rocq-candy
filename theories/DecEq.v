(*
Generic Typeclass for equality, plus some instances.

Authors:  Adam Petz, ampetz@ku.edu
          Will Thomas, 30wthomas@ku.edu
 *)

From Stdlib Require Import Setoid String List Decidable.
From RocqCandy Require Import Tactics.

Definition IDecEq (A : Type) := forall v1 v2 : A, {v1 = v2} + {v1 <> v2}.

Class DecEq (A : Type) := {
  dec_eq : IDecEq A
}.

Global Instance DecEq_string : DecEq string := {
  dec_eq := string_dec
}.

Global Instance DecEq_nat : DecEq nat := {
  dec_eq := Peano_dec.eq_nat_dec
}.

Ltac2 rec decdec_eq :=
  fun () =>
  match! goal with
  | [ h1 : ?_t, h2 : ?_t, _h3 : DecEq ?_t |- _ ] =>
    let h1 := Control.hyp h1 in
    let h2 := Control.hyp h2 in
    destruct (dec_eq $h1 $h2) > [
      (* Left side, equality gets subst, eauto cleans trivial, recurse *)
      subst_max; eauto; 
      try (Control.enter decdec_eq)
      | 
      (* Right side, we must've had some contra thing *)
      find_contra
    ]
  end.

Ltac2 build_deq := fun () =>
  ref (Build_DecEq _ _);
  intros x; induction x; 
  intros y; destruct y; 
  eauto; try find_contra;
  try (pp (&IHx &y); clear IHx;
  match! goal with
  | [ h : { _ } + { _ } |- _ ] =>
    let h := Control.hyp h in
    destruct $h > [
      (* Left side, equality gets subst, eauto cleans trivial, recurse *)
      subst_max; eauto;
      Control.enter decdec_eq
      | 
      (* Right side, we must've had some contra thing *)
      find_contra
    ]
  end);
  Control.enter decdec_eq.

Ltac2 Notation "build_deq" := build_deq ().

Import ListNotations.

Global Instance DecEq_list {A} `{HD : DecEq A} : DecEq (list A).
build_deq.
Defined.

Global Instance DecEq_option {A} `{HD : DecEq A} : DecEq (option A).
build_deq.
Defined.

Global Instance DecEq_pair {A B} `{DA : DecEq A} `{DB : DecEq B} : DecEq (A * B).
build_deq.
Defined.

Global Instance DecEq_sum {A B} `{DA : DecEq A} `{DB : DecEq B} : DecEq (A + B).
build_deq.
Defined.
