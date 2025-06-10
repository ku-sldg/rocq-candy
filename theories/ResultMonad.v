Module Result.
  Inductive t (A B : Type) : Type :=
  | res : A -> t A B
  | err : B -> t A B.
  Arguments res {A B} _.
  Arguments err {A B} _.

  (* Monadic bind — general type *)
  Definition bind {A B C} (x : t A B) (f : A -> t C B) : t C B :=
    match x with
    | res a => f a
    | err b => err b
    end.

  Definition ret {A B} (a : A) : t A B := res a.
  Definition raise {A B} (b : B) : t A B := err b.

  (* Unwrap with fallback *)
  Definition unwrap_or {A B} (x : t A B) (default : A) : A :=
    match x with
    | res a => a
    | err _ => default
    end.

  (* Notation scope *)
  Module Export Notation.
    (* Export as unqualified names *)
    Definition ret {A B} a := @ret A B a.
    Definition raise {A B} b := @raise A B b.
    Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
      (at level 61, c1 at next level, right associativity).
    Notation "' pat <- c1 ;; c2" :=
      (bind c1 (fun x => match x with pat => c2 end))
      (at level 61, pat pattern, c1 at next level, right associativity).
    Notation "x '<?>' y" := (unwrap_or x y)
      (at level 98, left associativity).
    Hint Unfold ret : core.
    Hint Unfold raise : core.
    Hint Unfold Result.ret : core.
    Hint Unfold Result.raise : core.
  End Notation.
End Result.
