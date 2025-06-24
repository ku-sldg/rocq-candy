From Stdlib Require Import List.
From RocqCandy Require Import Tactics ResultMonad.

(* State Monad definition *)
Definition State (St A E : Type) : Type := (St -> (Result A E * St))%type.

(* Monadic bind for State *)
Definition state_bind {St A B E} (m : State St A E) (f : A -> State St B E) : State St B E :=
  fun s =>
    let '(a, s') := m s in
    match a with
    | res a => f a s'
    | err e => (err e, s')
    end.

(* Get and put operations *)
Definition get {St E} : State St St E := fun s => (res s, s).
Definition put {St E} (s : St) : State St unit E := fun _ => (res tt, s).
Definition ret {St A E} (a : A) : State St A E := fun s => (res a, s).
Definition fail {St A E} (e : E) : State St A E := fun s => (err e, s).

(* Notation scope for State Monad *)
Module Export StateNotation.
  Notation "x <~ m ;;; c" := (@state_bind _ _ _ _ m (fun x => c))
    (at level 61, m at next level, right associativity).
  Notation "' pat <~ m ;;; c" :=
    (state_bind m (fun x => match x with pat => c end))
    (at level 61, pat pattern, m at next level, right associativity).
  Notation "e1 ;;; e2" := (_ <~ e1 ;;; e2) (at level 61, right associativity).
  Global Hint Unfold state_bind : core.
  Global Hint Unfold get put ret fail : core.
End StateNotation.
Export StateNotation.

(* Map over a list in the State monad *)
Fixpoint state_map {St A B E} (f : A -> State St B E) (l : list A) : State St (list B) E :=
  match l with
  | nil => fun s => (res nil, s)
  | cons h t =>
    v <~ f h ;;;
    vs <~ state_map f t ;;;
    ret (v :: vs)
  end.

(* Fold over a list in the State monad *)
Fixpoint state_fold {St A B E} (f : A -> B -> State St B E) (acc : B) (l : list A) : State St B E :=
  match l with
  | nil => fun s => (res acc, s)
  | cons h t =>
    acc' <~ f h acc ;;;
    state_fold f acc' t
  end.

(* Theorems about State Monad *)
Lemma state_bind_left_id : forall St A B E (a : A) (f : A -> State St B E) init,
  state_bind (ret a) f init = (f a) init.
Proof.
  ff.
Qed.

Lemma state_bind_right_id : forall St A E (m : State St A E) init,
  (state_bind m (fun a => (fun s => (res a, s)))) init = m init.
Proof.
  ff u.
Qed.

Lemma state_bind_assoc : forall St A B C E (m : State St A E) (f : A -> State St B E) (g : B -> State St C E) init,
  state_bind (state_bind m f) g init = state_bind m (fun x => state_bind (f x) g) init.
Proof.
  ff u.
Qed.
