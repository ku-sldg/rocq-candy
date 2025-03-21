(*
Generic Typeclass for equality, plus some instances.

Authors:  Adam Petz, ampetz@ku.edu
          Will Thomas, 30wthomas@ku.edu
 *)

From Coq Require Import EquivDec Setoid String List.
From RocqCandy Require Import Tactics.

Class EqClass (A : Type) := { 
  eqb : A -> A -> bool ;
  eqb_eq : forall x y, eqb x y = true <-> x = y 
}.

Theorem eqb_refl : forall {A : Type} `{EqClass A} a,
  eqb a a = true.
Proof.
  intros; erewrite eqb_eq; eauto.
Qed.

Theorem eqb_neq : forall {A : Type} `{EqClass A} a b,
  eqb a b = false <-> a <> b.
Proof.
  ff; try (rewrite eqb_refl in *; congruence);
  destruct (eqb a b) eqn:E; eauto;
  rewrite eqb_eq in *; ff.
Qed.

Theorem EqClass_impl_DecEq: forall (A : Type) `{H : EqClass A},
    forall (x y : A), {x = y} + {x <> y}.
Proof.
  intros; destruct H;
  destruct (eqb0 x y) eqn:E.
  - eapply eqb_eq0 in E; ff.
  - right; erewrite <- eqb_eq0; intros HC; congruence.
Qed.

Theorem eqb_symm_true : forall {A : Type} `{EqClass A} a1 a2,
  eqb a1 a2 = true <->
  eqb a2 a1 = true.
Proof.
  intros; repeat erewrite eqb_eq; intuition.
Qed.

Theorem eqb_symm : forall {A : Type} `{EqClass A} a1 a2,
  eqb a1 a2 = eqb a2 a1.
Proof.
  intros; destruct (eqb a1 a2) eqn:E1, (eqb a2 a1) eqn:E2; eauto;
  rewrite eqb_eq in *; subst; 
  rewrite eqb_refl in *; congruence.
Qed.

Theorem eqb_transitive : forall {A : Type} `{EqClass A} a1 a2 a3,
  eqb a1 a2 = true ->
  eqb a2 a3 = true ->
  eqb a1 a3 = true.
Proof.
  intros; repeat erewrite eqb_eq in *; subst; eauto.
Qed.

Ltac destEq t1 t2 :=
  let H := fresh "Heq" in
  destruct (eqb t1 t2) eqn:H;
  try rewrite H in *;
  [ rewrite eqb_eq in * | rewrite eqb_neq in *]; 
  subst; eauto.

Ltac break_eqs :=
  repeat match goal with
  | H : context [ eqb ?p1 ?p2 ] |- _ =>
      destEq p1 p2
  | |- context [ eqb ?p1 ?p2 ] =>
      destEq p1 p2
  | p1 : ?T, p2 : ?T |- _ => 
      tryif (
        (* If we already have NEQ hyps, don't make more *)
        match goal with
        | HP : p1 <> p2 |- _ => idtac
        end)
      then fail
      else destEq p1 p2
  end.

Ltac eq_crush :=
  subst_max;
  break_eqs;
  subst_max;
  full_do_bool;
  subst_max;
  try congruence.

Definition list_eqb_eqb {A : Type} (eqbA : A -> A -> bool) :=
  fix F l1 l2 :=
    match l1, l2 with
    | nil, nil => true
    | cons h1 t1, cons h2 t2 => andb (eqbA h1 h2) (F t1 t2)
    | _, _ => false
    end.

Theorem list_eqb_eq : forall {A : Type} (eqbA : A -> A -> bool),
  forall l1,
  (forall a1 a2, In a1 l1 -> eqbA a1 a2 = true <-> a1 = a2) ->
  forall (l2 : list A), list_eqb_eqb eqbA l1 l2 = true <-> l1 = l2.
Proof.
  induction l1; destruct l2; split; intros; simpl in *; eauto; try congruence.
  - unfold andb in H0. destruct (eqbA a a0) eqn:E.
    * rewrite H in E; subst; eauto; rewrite IHl1 in H0; subst; eauto.
    * congruence.
  - inversion H0; subst.
    unfold andb. destruct (eqbA a0 a0) eqn:E; eauto.
    * erewrite IHl1; eauto.
    * pose proof (H a0 a0). intuition. congruence.
Qed.

Fixpoint general_list_eq_class_eqb {A : Type} `{H : EqClass A} (l1 l2 : list A) : bool :=
  match l1, l2 with
  | nil, nil => true
  | cons h1 t1, cons h2 t2 => andb (eqb h1 h2) (general_list_eq_class_eqb t1 t2)
  | _, _ => false
  end.

Theorem general_list_eqb_eq : forall {A : Type} `{H : EqClass A},
  forall (a1 a2 : list A), general_list_eq_class_eqb a1 a2 = true <-> a1 = a2.
Proof.
  induction a1; destruct a2; split; intros; simpl in *; eauto; try congruence.
  - unfold andb in H0. destruct (eqb a a0) eqn:E.
    * rewrite eqb_eq in E; subst. rewrite IHa1 in H0. subst; eauto.
    * congruence.
  - inversion H0; subst.
    eq_crush.
    erewrite IHa1; eauto.
Qed.

Global Instance EqClass_extends_to_list (A : Type) `{H : EqClass A} : EqClass (list A) := {
  eqb := general_list_eq_class_eqb ;
  eqb_eq := general_list_eqb_eq
}.

Lemma nat_eqb_eq : forall n1 n2 : nat,
  Nat.eqb n1 n2 = true <-> n1 = n2.
Proof.
  induction n1; destruct n2; 
  split; intros; eauto;
  inversion H.
  - rewrite IHn1 in H1. subst; eauto.
  - subst. simpl. rewrite IHn1; eauto.
Qed.

Global Instance str_eq_class : EqClass string :=
  { eqb:= String.eqb;
    eqb_eq := String.eqb_eq }.

Global Instance nat_EqClass : EqClass nat :=
  { eqb:= Nat.eqb;
    eqb_eq := nat_eqb_eq }.

Definition eqbPair{A B:Type}`{H:EqClass A}`{H':EqClass B} (p1:A*B) (p2:A*B) : bool :=
  match (p1,p2) with
  | ((a1,b1), (a2,b2)) => andb (eqb a1 a2) (eqb b1 b2)
  end.

Lemma beq_pair_true{A B:Type}`{H:EqClass A}`{H':EqClass B} : forall (p1 p2:(A*B)),
    eqbPair p1 p2 = true -> p1 = p2.
Proof.
  intros.
  unfold eqbPair in *.
  destruct p1, p2.
  eq_crush.
Qed.

Lemma pair_eqb_eq{A B:Type}`{H:EqClass A}`{H':EqClass B} : forall (p1 p2:(A*B)),
    eqbPair p1 p2 = true <-> p1 = p2.
Proof.
  intros.
  split.
  - eapply beq_pair_true; eauto.
  - ff.
    unfold eqbPair.
    ff.
    eq_crush.
Qed.

Global Instance pair_EqClass{A B:Type}`{H:EqClass A}`{H':EqClass B} : EqClass (A*B) :=
  { eqb:= eqbPair;
    eqb_eq := pair_eqb_eq }.

Global Instance EqClass_impl_EqDec (A : Type) `{H : EqClass A} : EqDec A eq.
intros x y.
eq_crush.
left; reflexivity.
Defined.