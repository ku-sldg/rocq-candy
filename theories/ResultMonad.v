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
  Hint Unfold bind : core.
  Hint Unfold unwrap_or : core.
End ResultNotation.