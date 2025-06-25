From Stdlib Require Import List.
From RocqCandy Require Import Tactics.

(* Config Monad definition: Reader/Environment/Configuration Monad *)
Definition Config (Cfg A : Type) : Type := 
  (Cfg -> A).

(* Monadic bind for Config *)
Definition config_bind {Cfg A B} (m : Config Cfg A) (f : A -> Config Cfg B) : Config Cfg B :=
  fun cfg => f (m cfg) cfg.

(* Read the config *)
Definition ask {Cfg} : Config Cfg Cfg := fun cfg => cfg.
Definition done {Cfg A} (a : A) : Config Cfg A := fun _ => a.

(* Notation scope for Config Monad *)
Module Export ConfigNotation.
  Notation "x <- m ';;c' c" := (@config_bind _ _ _ m (fun x => c))
    (at level 61, m at next level, right associativity).
  Notation "' pat <- m ';;c' c" :=
    (config_bind m (fun x => match x with pat => c end))
    (at level 61, pat pattern, m at next level, right associativity).
  Notation "e1 ';;c' e2" := (_ <- e1 ;;c e2) (at level 61, right associativity).
  Global Hint Unfold config_bind : core.
  Global Hint Unfold ask done : core.
End ConfigNotation.
Export ConfigNotation.

(* Map over a list in the Config monad *)
Fixpoint config_map {Cfg A B} (f : A -> Config Cfg B) (l : list A) : Config Cfg (list B) :=
  match l with
  | nil => done nil
  | cons h t =>
      v <- f h ;;c
      vs <- config_map f t ;;c
      done (v :: vs)
  end.

(* Fold over a list in the Config monad *)
Fixpoint config_fold {Cfg A B} (f : A -> B -> Config Cfg B) (acc : B) (l : list A) : Config Cfg B :=
  match l with
  | nil => fun _ => acc
  | cons h t =>
      acc' <- f h acc ;;c
      config_fold f acc' t
  end.

(* Theorems about Config Monad *)
Lemma config_bind_left_id : forall Cfg A B (a : A) (f : A -> Config Cfg B) cfg,
  config_bind (fun _ => a) f cfg = f a cfg.
Proof. ff. Qed.

Lemma config_bind_right_id : forall Cfg A (m : Config Cfg A) cfg,
  config_bind m (fun a => done a) cfg = m cfg.
Proof. ff u. Qed.

Lemma config_bind_assoc : forall Cfg A B C (m : Config Cfg A) (f : A -> Config Cfg B) (g : B -> Config Cfg C) cfg,
  config_bind (config_bind m f) g cfg = config_bind m (fun x => config_bind (f x) g) cfg.
Proof. ff u. Qed.
