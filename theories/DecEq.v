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

Global Instance DecEq_string : DecEq string := {
  dec_eq := string_dec
}.

Global Instance DecEq_nat : DecEq nat := {
  dec_eq := Peano_dec.eq_nat_dec
}.

Import ListNotations.

Fixpoint list_eq {A} `{DecEq A} (l1 l2 : list A) : {l1 = l2} + {l1 <> l2}.
ref (
  match l1, l2 with
  | [], [] => left eq_refl
  | [], _ => right _
  | _, [] => right _
  | x1 :: xs1, x2 :: xs2 => 
    match dec_eq x1 x2 with
    | left Heq => 
      match list_eq _ _ xs1 xs2 with
      | left Heq' => left _
      | right Hneq => right _
      end
    | right Hneq => right _
    end
  end
); try congruence.
Qed.

Global Instance DecEq_list {A} `{HD : DecEq A} : DecEq (list A) := {
  dec_eq := list_eq
}.

Global Instance DecEq_option {A} `{HD : DecEq A} : DecEq (option A).
ref (
  Build_DecEq _
  (fun o1 o2 => 
    match o1, o2 with
    | None, None => left eq_refl
    | Some x1, Some x2 => 
      match dec_eq x1 x2 with
      | left Heq => left _
      | right Hneq => right _
      end
    | _, _ => right _
    end
  )
); try congruence.
Qed.

Global Instance DecEq_pair {A B} `{DA : DecEq A} `{DB : DecEq B} : DecEq (A * B).
ref (
  Build_DecEq _
  (fun p1 p2 => 
    let '(x1, y1) := p1 in
    let '(x2, y2) := p2 in
    match dec_eq x1 x2, dec_eq y1 y2 with
    | left Heq_x, left Heq_y => left _
    | _, _ => right _
    end
  )
); try congruence.
Qed.