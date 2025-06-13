From Stdlib Require Export StrictProp.
From RocqCandy Require Import Tactics.

(* inspired by Bonak: https://github.com/artagnon/bonak/blob/master/theories/%CE%BDType/LeYoneda.v *)
Inductive SFalse : SProp :=.
Inductive STrue : SProp := sI.
(* Equality in SProp is =S *)
Global Hint Constructors STrue SFalse Box Squash : core.

Inductive eqsprop {A: SProp} (x: A): A -> Prop := 
  eqsprop_refl: eqsprop x x.
Infix "=S" := eqsprop (at level 70): type_scope.

Ltac2 Notation "box_simpl" :=
  repeat (
    match! goal with
    | [ h : Box SFalse |- _ ] => 
      let h := Control.hyp h in
      destruct $h; ltac1:(intuition)
    | [ h : Box STrue |- _ ] => clear $h
    | [ h : SFalse |- _ ] => 
      let h := Control.hyp h in destruct $h
    end).

Definition box_proj {A} :=
  fun (x : Box A) => match x with
  | box x' => x'
  end.

Definition box_irrelevant (A:SProp) (x y : Box A) : x = y := 
  let '(box x) := x in
  let '(box y) := y in
  eq_refl.

Ltac2 Notation "collapse_boxes" := 
  repeat (
    match! goal with
    | [ b1 : Box _,
        b2 : Box _ |- _ ] =>
      let b1 := Control.hyp b1 in
      let b2 := Control.hyp b2 in
      pp (box_irrelevant _ $b1 $b2); 
      subst_max
    end).