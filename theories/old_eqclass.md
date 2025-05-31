Class EqClass (A : Type) := { 
  eqb : A -> A -> bool ;
  eqb_eq : forall x y, eqb x y = true <-> x = y 
}.

Class DecEq (A : Type) := {
  dec_eq : forall x y : A, {x = y} + {x <> y}
}.

Theorem deceq_impl_eqclass : forall {A} `{DecEq A}, EqClass A.
intros.
ref (Build_EqClass _ 
  (fun x y => if dec_eq x y then true else false) 
  _).
  ff.
Qed.

(* NOTE: This is a bit of a hack, but it is the only way to get the
   EqClass to be usable in Ltac2. *)

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

Ltac2 destEq (t1 : constr) (t2 : constr) :=
  let h := in_goal @Heq in
  destruct (@eqb _ _ $t1 $t2) eqn:$h >
  [ 
    let h := Control.hyp h in
    try (rewrite $h in *); 
    rewrite eqb_eq in * 
    | 
    let h := Control.hyp h in
    try (rewrite $h in *); 
    rewrite eqb_neq in *
  ];
  subst; 
  eauto;
  try (simple congruence 1).

Ltac2 Notation "destEq" 
  t1(constr)
  t2(constr)
  :=
  destEq t1 t2.

Ltac2 break_eqs () :=
  repeat (
    (* First, do the coarse but powerful reductions *)
    repeat (
      match! goal with
      | [ h : context [ eqb ?_p1 ?_p1 ] |- _ ] =>
        erewrite eqb_refl in $h; subst_max
      | [ |- context [ eqb ?_p1 ?_p1 ] ] =>
        erewrite eqb_refl; try reflexivity
      | [ _h : context [ eqb ?p1 ?p2 ] |- _ ] =>
        destEq $p1 $p2
      | [ |- context [ eqb ?p1 ?p2 ] ] =>
        destEq $p1 $p2
      end
    );
    (* Next, we want to just do a more aggressive destruction *)
    (*
    NOTE: In theory, this is great... but it can really explode quickly.
    For example
    x : A,
    y : B,
    where underneath A == B, we end up with a big issue.
    We don't really want to do it for this case (a lot of ID-esque types are all the same, but shouldn't really be considered comparable).
    *)
    repeat (match! goal with
    | [ p1 : ?_t, p2 : ?_t, _ht : EqClass ?_t 
        |- context [ ?p1' = ?p2' ] ] =>
      (* If it is somehow relevant to our goal that these two are equal.*)
      (
      let p1 := Control.hyp p1 in
      let p2 := Control.hyp p2 in
      if Bool.neg (Constr.equal p1 p1' && Constr.equal p2 p2') 
      then fail
      else
        if (already_proven preterm:(($p1 <> $p2)%type))
        then (* skip, we already have a lemma disproving *) fail
        else (destEq $p1 $p2))
    end);
    subst_max;
    full_do_bool;
    try (simple congruence 1)
  ).

Ltac2 Notation "break_eqs" := break_eqs ().

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
ltac1:(unfold "===").
ff e.
Defined.