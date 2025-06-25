From Stdlib Require Import List.
From RocqCandy Require Import Tactics ResultMonad.

(* State Monad definition *)
Definition State (St Val : Type) : Type := (St -> (Val * St))%type.

(* Monadic bind for State *)
Definition state_bind {St A B} (m : State St A) (f : A -> State St B) : State St B :=
  fun s =>
    let '(a, s') := m s in
    f a s'.

(* Get and put operations *)
Definition get {St} : State St St := fun s => (s, s).
Definition put {St} (s : St) : State St unit := fun _ => (tt, s).
Definition ret {St A} (a : A) : State St A := fun s => (a, s).

(* Notation scope for State Monad *)
Module Export StateNotation.
  Notation "x <- m ;;s c" := (@state_bind _ _ _ m (fun x => c))
    (at level 61, m at next level, right associativity).
  Notation "' pat <- m ;;s c" :=
    (state_bind m (fun x => match x with pat => c end))
    (at level 61, pat pattern, m at next level, right associativity).
  Notation "e1 ;;s e2" := (_ <- e1 ;;s e2) (at level 61, right associativity).
  Global Hint Unfold state_bind : core.
  Global Hint Unfold get put ret : core.
End StateNotation.
Export StateNotation.

(* Map over a list in the State monad *)
Fixpoint state_map {St A B} (f : A -> State St B) (l : list A) : State St (list B) :=
  match l with
  | nil => fun s => (nil, s)
  | cons h t =>
    v <- f h ;;s
    vs <- state_map f t ;;s
    ret (v :: vs)
  end.

(* Fold over a list in the State monad *)
Fixpoint state_fold {St A B} (f : A -> B -> State St B) (acc : B) (l : list A) : State St B :=
  match l with
  | nil => ret acc
  | cons h t =>
    acc' <- f h acc ;;s
    state_fold f acc' t
  end.

(* Theorems about State Monad *)
Lemma state_bind_left_id : forall St A B (a : A) (f : A -> State St B) init,
  state_bind (ret a) f init = (f a) init.
Proof.
  ff.
Qed.

Lemma state_bind_right_id : forall St A (m : State St A) init,
  (state_bind m (fun a => ret a)) init = m init.
Proof.
  ff u.
Qed.

Lemma state_bind_assoc : forall St A B C (m : State St A) (f : A -> State St B) (g : B -> State St C) init,
  state_bind (state_bind m f) g init = state_bind m (fun x => state_bind (f x) g) init.
Proof.
  ff u.
Qed.
