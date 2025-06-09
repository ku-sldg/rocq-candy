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

Import ListNotations.

Global Instance DecEq_list {A} `{HD : DecEq A} : DecEq (list A).
ref (
  Build_DecEq _
  (fix F l1 l2 :=
  match l1, l2 with
  | [], [] => left eq_refl
  | [], _ => right _
  | _, [] => right _
  | x1 :: xs1, x2 :: xs2 => 
    match dec_eq x1 x2 with
    | left Heq => 
      match F xs1 xs2 with
      | left Heq' => left _
      | right Hneq => right _
      end
    | right Hneq => right _
    end
  end)
); try congruence.
Defined.

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
Defined.

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
Defined.

Global Instance DecEq_sum {A B} `{DA : DecEq A} `{DB : DecEq B} : DecEq (A + B).
ref (
  Build_DecEq _
  (fun p1 p2 => 
    match p1, p2 with
    | inl x1, inl x2 => 
      match dec_eq x1 x2 with
      | left HDA => left _
      | _ => right _
      end
    | inr x1, inr x2 => 
      match dec_eq x1 x2 with
      | left HDA => left _
      | _ => right _
      end
    | _, _ => right _
    end
  )
); try congruence.
Defined.
