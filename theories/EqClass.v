(*
Generic Typeclass for equality, plus some instances.

Authors:  Adam Petz, ampetz@ku.edu
          Will Thomas, 30wthomas@ku.edu
 *)

From Stdlib Require Import EquivDec Setoid String List.
From RocqCandy Require Import Tactics.

Class EqClass (A : Type) := { 
  eqb : A -> A -> bool ;
  eqb_eq : forall x y, eqb x y = true <-> x = y 
}.

(* NOTE: These theorems don't go inside the section 
because the Ltac needs them, and Ltac cannot be exported from a section
*)
Theorem eqb_refl : forall {A} `{EqClass A} a,
  eqb a a = true.
Proof.
  intros; erewrite eqb_eq; eauto.
Qed.

Theorem eqb_neq : forall {A} `{EqClass A} a b,
  eqb a b = false <-> a <> b.
Proof.
  pps @eqb_refl, @eqb_eq.
  ff r; destruct (eqb a b) eqn:E; ff r.
Qed.

Ltac destEq t1 t2 :=
  let H := fresh "Heq" in
  destruct (eqb t1 t2) eqn:H;
  try rewrite H in *;
  [ rewrite eqb_eq in * | rewrite eqb_neq in *]; 
  subst; eauto.

Ltac2 Notation "destEq" 
  t1(preterm)
  t2(preterm)
  :=
  ltac1:(t1 t2 |- 
    destEq t1 t2)
  (Ltac1.of_preterm t1) (Ltac1.of_preterm t2).

Ltac break_eqs :=
  repeat (
    match goal with
    | H : context [ eqb ?p1 ?p1 ] |- _ =>
        erewrite eqb_refl in H
    | |- context [ eqb ?p1 ?p1 ] =>
        erewrite eqb_refl
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
    end;
    ltac2:(subst_max;
    full_do_bool;
    try (simple congruence 1))
  ).

Ltac2 Notation "break_eqs" :=
  ltac1:(break_eqs).
Ltac2 Notation break_eqs :=
  break_eqs.

Ltac2 Notation eq_crush :=
  eauto;
  try (simple congruence 1);
  subst_max;
  break_eqs;
  subst_max;
  full_do_bool;
  subst_max;
  try (congruence);
  eauto.

Ltac2 e := fun () => eq_crush.

Section Theories.
  Context {A : Type}.
  Context  {EqA : EqClass A}.

  Theorem EqClass_impl_DecEq: forall (x y : A), {x = y} + {x <> y}.
  Proof.
    ff e.
  Qed.

  Theorem eqb_symm : forall a1 a2,
    eqb a1 a2 = eqb a2 a1.
  Proof.
    ff e.
  Qed.

  Theorem eqb_transitive : forall a1 a2 a3,
    eqb a1 a2 = true ->
    eqb a2 a3 = true ->
    eqb a1 a3 = true.
  Proof.
    ff e.
  Qed.

End Theories.

(* Tactics *)

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
  induction l1; destruct l2; split; ff e,r.
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
  induction a1; destruct a2; split; ff e,r.
Qed.

Lemma nat_eqb_eq : forall n1 n2 : nat,
  Nat.eqb n1 n2 = true <-> n1 = n2.
Proof.
  induction n1; destruct n2; ff e,r.
Qed.

(* Instances *)

Global Instance EqClass_list (A : Type) `{H : EqClass A} : EqClass (list A) := {
  eqb := general_list_eq_class_eqb ;
  eqb_eq := general_list_eqb_eq
}.

Global Instance EqClass_string : EqClass string := { 
  eqb:= String.eqb;
  eqb_eq := String.eqb_eq 
}.

Global Instance EqClass_nat : EqClass nat := { 
  eqb:= Nat.eqb;
  eqb_eq := nat_eqb_eq 
}.

Global Instance EqClass_prod {A B:Type} `{EqClass A, EqClass B} : EqClass (A*B).
ref (Build_EqClass _ 
  (fun '(a1,b1) '(a2,b2) => andb (eqb a1 a2) (eqb b1 b2)) 
  (fun '(a1, b1) '(a2, b2) => _)).
ff e.
Defined.

Global Instance EqClass_impl_EqDec (A : Type) `{H : EqClass A} : EqDec A eq.
intros x y.
eq_crush.
left; reflexivity.
Defined.