Module Result.
  Inductive t (A B : Type) : Type :=
  | res : A -> t A B
  | err : B -> t A B.
  Arguments res {A B} _.
  Arguments err {A B} _.

  Definition bind {A B} (x : t A B) (f : A -> t A B) : t A B :=
    match x with
    | res a => f a
    | err b => err b
    end.

  Definition ret {A B} (a : A) : t A B := res a.
  Definition raise {A B} (b : B) : t A B := err b.

  Module Notation.
    Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
      (at level 61, c1 at next level, right associativity).

    Notation "' pat <- c1 ;; c2" :=
      (bind c1 (fun x => match x with pat => c2 end))
      (at level 61, pat pattern, c1 at next level, right associativity).
    Notation "'ret' x" := (ret x) (at level 61, x at next level).
    Notation "'raise' x" := (raise x) (at level 61, x at next level).

  End Notation.
End Result.


