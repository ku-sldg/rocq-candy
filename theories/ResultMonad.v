From Stdlib Require Import List.
From RocqCandy Require Import Tactics.

Inductive Result (A B : Type) : Type :=
| res : A -> Result A B
| err : B -> Result A B.
Arguments res {A B} _.
Arguments err {A B} _.

(* Monadic bind — general type *)
Definition bind {A B C} (x : Result A B) (f : A -> Result C B) : Result C B :=
  match x with
  | res a => f a
  | err b => err b
  end.

(* Unwrap with fallback *)
Definition unwrap_or {A B} (x : Result A B) (default : A) : A :=
  match x with
  | res a => a
  | err _ => default
  end.

(* Notation scope *)
Module Export ResultNotation.
  (* Export as unqualified names *)
  Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity).
  Notation "' pat <- c1 ;; c2" :=
    (bind c1 (fun x => match x with pat => c2 end))
    (at level 61, pat pattern, c1 at next level, right associativity).
  Notation "x '<?>' y" := (unwrap_or x y)
    (at level 98, left associativity).
  Global Hint Unfold bind : core.
  Global Hint Unfold unwrap_or : core.
End ResultNotation.
Export ResultNotation.

Fixpoint result_map {A B E : Type} (f : A -> Result B E) (l : list A) 
    : Result (list B) E :=
  match l with
  | nil => res nil
  | (cons h t) =>
      v <- f h;;
      vs <- result_map f t;;
      res (cons v vs)
  end.

Lemma result_map_spec : forall {X Y Z : Type} (l : list X) (f : X -> Result Y Z) x (resl : list Y),
  In x l ->
  result_map f l = res resl ->
  (exists fx', (f x) = res fx' /\ In fx' resl).
Proof.
  induction l; simpl in *; intuition; eauto; ff u, a.
  find_eapply_lem_hyp IHl; ff.
Qed.

Fixpoint result_fold {A B E : Type} (f : A -> B -> Result B E) 
    (acc : B) (l : list A) 
    : Result B E :=
  match l with
  | nil => res acc
  | (cons h t) =>
      acc' <- f h acc;;
      result_fold f acc' t
  end.

