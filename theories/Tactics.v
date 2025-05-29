(* Local copy of structural tactics library from:  https://github.com/uwplse/StructTact 

We have locally modified this a great deal to add tactics that are useful for our proofs. *)
From Stdlib Require Import Bool String List Ascii Lia.
Import ListNotations.

From ExtLib Require Export Tactics BoolTac.

From Ltac2 Require Export Ltac2 Printf Pstring Notations.
From Ltac2 Require Export Bool Lazy Array Lazy FMap Fresh Control.

(** [clean] removes any hypothesis of the shape [X = X]. *)
Ltac2 Notation "clean" :=
  repeat (
    match! goal with
    | [ h : ?_x = ?_x |- _ ] => clear $h
    end
  ).
Ltac2 Notation clean := clean.

Example test_clean : forall A (x : A), x = x -> True.
Proof.
  intros.
  clean.
  apply I.
Qed.

(** [subst_max] performs as many [subst] as possible, clearing all
    trivial equalities from the context. *)
Ltac2 Notation subst_max :=
  clean; repeat subst; clean. 
  (* Note: ltac2 "subst" calls "subst_all", so hopefully it truly replicates this functionality *)

Example test_subst_max : forall A (x y z : A), x = x -> x = y -> y = z -> x = z.
Proof.
  intros.
  subst_max.
  reflexivity.
Qed.

(** The Coq [inversion] tries to preserve your context by only adding
    new equalities, and keeping the inverted hypothesis.  Often, you
    want the resulting equalities to be substituted everywhere.  [inv]
    performs this post-substitution.  Often, you don't need the
    original hypothesis anymore.  [invc] extends [inv] and removes the
    inverted hypothesis.  Sometimes, you also want to perform
    post-simplification.  [invcs] extends [invc] and tries to simplify
    what it can. *)
Ltac2 Notation "inv"
  arg(destruction_arg) 
  pat(opt(seq("as", intropattern)))
  ids(opt(seq("in", list1(ident)))) :=
  Std.inversion Std.FullInversion arg pat ids;
  subst_max.

Example test_inv : forall A (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros.
  inv H.
  reflexivity.
Qed.

Ltac2 Notation "invc"
  arg(destruction_arg) 
  pat(opt(seq("as", intropattern)))
  ids(opt(seq("in", list1(ident)))) :=
  Std.inversion Std.FullInversion arg pat ids;
  subst_max; 
  match arg with
  | Std.ElimOnIdent h => clear $h
  | _ => ()
  end.

Ltac2 Notation "invcs"
  arg(destruction_arg) 
  pat(opt(seq("as", intropattern)))
  ids(opt(seq("in", list1(ident)))) :=
  Std.inversion Std.FullInversion arg pat ids;
  subst_max;
  match arg with
  | Std.ElimOnIdent h => clear $h
  | _ => ()
  end;
   simpl in *.

(** [break_if] finds instances of [if _ then _ else _] in your goal or
    context, and destructs the discriminee, while retaining the
    information about the discriminee's value leading to the branch
    being taken. *)
Ltac2 Notation "break_if" :=
  match! goal with
  | [ |- context [ if ?x then _ else _ ] ] =>
    match! Constr.type x with
    | sumbool _ _ => destruct ($x)
    | _ => destruct ($x) eqn:?
    end
  | [ _h : context [ if ?x then _ else _ ] |- _] =>
    match! Constr.type x with
    | sumbool _ _ => destruct ($x)
    | _ => destruct ($x) eqn:?
    end
  end.
Ltac2 Notation break_if := break_if.

Example test_break_if {A : Type} (f : A -> A -> bool) : forall x y z : A,
  (if f x y then (if f y z then z else z) else (if f z x then z else z)) = z.
Proof.
  intros.
  repeat (break_if; eauto).
Qed.

Example test_break_if2 {A : Type} (f : A -> A -> bool) : forall x y z : A,
  (if f x y then (if f y z then z else z) else (if f z x then z else z)) = y -> y = z.
Proof.
  intros.
  repeat (break_if; eauto).
Qed.

(** [break_match_hyp] looks for a [match] construct in some
    hypothesis, and destructs the discriminee, while retaining the
    information about the discriminee's value leading to the branch
    being taken. *)
Ltac2 Notation "break_match_hyp" :=
  match! goal with
  | [ _h : context [ match ?x with _ => _ end ] |- _] =>
    match! Constr.type x with
    | sumbool _ _ => destruct $x
    | _ => destruct $x eqn:?
    end
  end.

Ltac2 Notation break_match_hyp := break_match_hyp.

Example test_break_match_hyp : forall x y z : nat,
  (match x with
   | 0 => (match y with
           | 0 => z
           | S _ => z
         end)
   | S _ => z
   end) = y -> y = z.
Proof.
  intros.
  repeat (break_match_hyp; eauto).
Qed.

(** [break_match_goal] looks for a [match] construct in your goal, and
    destructs the discriminee, while retaining the information about
    the discriminee's value leading to the branch being taken. *)
Ltac2 Notation "break_match_goal" :=
  match! goal with
    | [ |- context [ match ?x with _ => _ end ] ] =>
      match! Constr.type x with
        | sumbool _ _ => destruct $x
        | _ => destruct $x eqn:?
      end
  end.

Ltac2 Notation break_match_goal := break_match_goal.

Example test_break_match_goal : forall x y z : nat,
  (match x with
   | 0 => (match y with
           | 0 => z
           | S _ => z
         end)
   | S _ => z
   end) = y -> y = z.
Proof.
  intros x y z.
  repeat (break_match_goal; eauto).
Qed.

Ltac2 oneOf tac_list :=
  progress (List.fold_left 
    (fun acc x => (fun next => acc (); try (x ()); next)) 
    (fun () => ()) 
    tac_list).

Ltac2 Notation "oneOf" 
  "[" tacs(list0(thunk(tactic(6)), "|")) "]" :=
  (* Attempts to run all of the tactics, and ensures that at least one of them succeeded *)
  oneOf tacs.

(* 
Example test_oneOf : True /\ True /\ True.
Proof.
  (* You can't completely fail *)
  Fail oneOf [ printf "1"; fail | printf "2"; fail ].
  (* Progress from other branchs is not lost *)
  oneOf [ printf "1"; fail | printf "2"; split | apply I ].
  (* Does not continue past completed goals *)
  oneOf [ printf "1"; fail | split | apply I | printf "3" ].
Qed.
*)

(** [break_match] breaks a match, either in a hypothesis or in your
    goal. *)
Ltac2 Notation "break_match" := 
  oneOf [ break_match_goal | break_match_hyp ].

Ltac2 rec break_match_hyp_rec (hyp : ident) :=
  match! (Constr.type (Control.hyp hyp)) with
  | context [ match ?x with _ => _ end ] =>
    let h1 := in_goal hyp in
    destruct $x eqn:$h1;
    (* First, try to continue on the current hyp *)
    try (break_match_hyp_rec hyp);
    try (break_match_hyp_rec h1)
  end.

Ltac2 Notation "break_match_hyp_rec"
  hyp(ident) :=
  break_match_hyp_rec hyp.

Example test_break_match_hyp_rec : forall x y z : nat,
  (match x with
  | 0 => (match y with
          | 0 => z
          | S _ => z
        end)
  | S _ => z
  end) = y -> y = z.
Proof.
  intros x y z H.
  break_match_hyp_rec H; eauto.
Qed.

(** [break_inner_match' t] tries to destruct the innermost [match] it
    find in [t]. *)
Ltac2 rec break_inner_match' (body : constr) :=
  match! body with
  | context [ match ?x with _ => _ end ] =>
    try (first [ 
      break_inner_match' x |
      destruct $x eqn:?
    ])
  | _ => destruct $body eqn:?
  end.

Example test_break_inner_match' : forall y z : nat,
  (match (match y with
          | 0 => z
          | S _ => z
        end) with
  | 0 => z
  | S _ => z
  end) = y -> y = z.
Proof.
  intros y z H.
  break_inner_match' (Constr.type 'H);
  eauto;
  try (break_inner_match' (Constr.type 'H); eauto).
Qed.

(** [break_inner_match_goal] tries to destruct the innermost [match] it
    find in your goal. *)
Ltac2 Notation "break_inner_match_goal" :=
 match! goal with
  | [ |- context[match ?x with _ => _ end] ] =>
    break_inner_match' x
 end.

Ltac2 Notation break_inner_match_goal := break_inner_match_goal.

Example test_break_inner_match_goal : 
  match (match 1 with
        | 0 => 2
        | S _ => 3
        end) with
  | 0 => 2
  | S _ => 3
  end = 1 -> 1 = 3.
Proof.
  break_inner_match_goal; eauto.
Qed.

(** [break_inner_match_hyp] tries to destruct the innermost [match] it
    find in a hypothesis. *)
Ltac2 Notation "break_inner_match_hyp" :=
  match! goal with
  | [ h : context[match ?_x with _ => _ end] |- _ ] =>
    break_inner_match' (Constr.type (Control.hyp h))
  end.

Ltac2 Notation break_inner_match_hyp := 
  break_inner_match_hyp.

Example test_break_inner_match_hyp :
    match (match 1 with
        | 0 => 2
        | S _ => 3
        end) with
  | 0 => 2
  | S _ => 3
  end = 1 -> 1 = 3.
Proof.
  intros H.
  break_inner_match_hyp; eauto.
Qed.

(** [break_inner_match] tries to destruct the innermost [match] it
    find in your goal or a hypothesis. *)
Ltac2 Notation break_inner_match := 
  oneOf [ break_inner_match_goal | break_inner_match_hyp ].

(** [break_exists] destructs an [exists] in your context. *)
Ltac2 Notation "break_exists" :=
  match! goal with
  | [ h : exists _ , _ |- _ ] =>
    let destVal := Control.hyp h in
    destruct $destVal
  end.

Ltac2 Notation break_exists := break_exists.

Example test_break_exists : forall y,
  (exists x1 x2, x1 = S y + x2) ->
  (exists x, x = S (S y)).
Proof.
  intros.
  repeat break_exists.
  eauto.
Qed.

(** [break_and] destructs all conjunctions in context. *)
Ltac2 Notation "break_and" :=
  repeat (
    match! goal with
    | [ h : _ /\ _ |- _ ] => 
      let destVal := Control.hyp h in
      destruct $destVal
    end
  ).

Ltac2 Notation break_and := break_and.

(* Ltac2 Notation break_and := break_and. *)
Example test_break_and {A} : forall x y z : A,
  (x = y /\ y = z) ->
  x = z.
Proof.
  intros; break_and; subst_max; eauto.
Qed.

Ltac2 rew_in
  (h1 : ident)
  (h2 : ident)
  (tac : (unit -> unit) option) :=
  let h1 := Control.hyp h1 in
  match tac with
  | None => 
    rewrite $h1 in $h2
  | Some t => 
    rewrite $h1 in $h2 by (t ())
  end.

(* This tactic is basically used just to restore the simpler behavior of rewriting where you pass 2 idents. It cover's up some of the necessary anti-quotations that Ltac2 requires *)
Ltac2 Notation "rew_in"
  h1(ident) 
  h2(ident) 
  tac(opt(seq("by", thunk(tactic)))) :=
  rew_in h1 h2 tac.

(** [rew_in H H'] rewrites [H] in [H']. *)

Example test_rew_in : forall x y z : nat,
  x = y -> (x = y -> y = z) -> ~ (x = z) -> False.
Proof.
  intros; rew_in H0 H by eauto; eauto.
Qed.
  
(** [find_rewrite] performs a [rewrite] with some hypothesis in some
    other hypothesis. *)
Ltac2 Notation "find_rewrite" :=
  subst_max;
  match! goal with
  | [ h : ?_x = _ |- context [ ?_x ] ] => 
    let h := Control.hyp h in
    rewrite $h
  | [ h : ?_x = _, h' : context [ ?_x ] |- _ ] => 
    rew_in $h $h'
  | [ h : ?_x = _, h' : ?_x = _ |- _ ] => 
    printf "unique case! please report"; 
    rew_in $h $h'
  | [ h : ?_x _ = _, h' : ?_x _ = _ |- _ ] => 
    rew_in $h $h'
  | [ h : ?_x _ _ = _, h' : ?_x _ _ = _ |- _ ] => 
    rew_in $h $h'
  | [ h : ?_x _ _ _ = _, h' : ?_x _ _ _ = _ |- _ ] => 
    rew_in $h $h'
  | [ h : ?_x _ _ _ _ = _, h' : ?_x _ _ _ _ = _ |- _ ] => 
    rew_in $h $h'
  end.

Ltac2 Notation find_rewrite := find_rewrite.

(** [find_rewrite_lem lem] rewrites with [lem] in some hypothesis. *)
Ltac2 Notation "find_rewrite_lem" 
  lem(ident) :=
  match! goal with
  | [ h : _ |- _ ] =>
    (rew_in $lem $h) > [()]
  end.

(** [find_rewrite_lem_by lem t] rewrites with [lem] in some
    hypothesis, discharging the generated obligations with [t]. *)
Ltac2 Notation "find_rewrite_lem_by" 
  lem(constr) 
  tac(tactic(6)) :=
  match! goal with
  | [ h : _ |- _ ] =>
    rew_in $lem $h by tac
  end.

(** [find_erewrite_lem_by lem] erewrites with [lem] in some hypothesis
    if it can discharge the obligations with [eauto]. *)
Ltac2 Notation "find_erewrite_lem" 
  lem(ident) :=
  match! goal with
  | [ h : _ |- _] => 
    erewrite $lem in $h by eauto
  | [ |- _ ] => 
    erewrite $lem by eauto
  end.

(** [find_reverse_rewrite] performs a [rewrite <-] with some hypothesis in some
    other hypothesis. *)
Ltac2 Notation "find_reverse_rewrite" :=
  subst_max;
  match! goal with
  | [ h : ?_x = _ |- context [ ?_x ] ] => 
    let h := Control.hyp h in
    rewrite <- $h
  | [ h : ?_x = _, h' : context [ ?_x ] |- _ ] => 
    let h := Control.hyp h in
    rewrite <- $h in $h'
  | [ h : ?_x = _, h' : ?_x = _ |- _ ] => 
    printf "unique case! please report"; 
    let h := Control.hyp h in
    rewrite <- $h in $h'
  | [ h : ?_x _ = _, h' : ?_x _ = _ |- _ ] => 
    let h := Control.hyp h in
    rewrite <- $h in $h'
  | [ h : ?_x _ _ = _, h' : ?_x _ _ = _ |- _ ] => 
    let h := Control.hyp h in
    rewrite <- $h in $h'
  | [ h : ?_x _ _ _ = _, h' : ?_x _ _ _ = _ |- _ ] => 
    let h := Control.hyp h in
    rewrite <- $h in $h'
  | [ h : ?_x _ _ _ _ = _, h' : ?_x _ _ _ _ = _ |- _ ] => 
    let h := Control.hyp h in
    rewrite <- $h in $h'
  end;
  (* Can this ever actually succeed where "find_rewrite" didn't? *)
  printf "find_reverse_rewrite WORKED!".

(** [find_inversion] find a symmetric equality and performs [invc] on it. *)
Ltac2 Notation "find_inversion" :=
  match! goal with
  | [ h : ?_x _ = ?_x _ |- _ ] => 
    let h := Control.hyp h in invc $h
  | [ h : ?_x _ _ = ?_x _ _ |- _ ] => 
    let h := Control.hyp h in invc $h
  | [ h : ?_x _ _ _ = ?_x _ _ _ |- _ ] => 
    let h := Control.hyp h in invc $h
  | [ h : ?_x _ _ _ _ = ?_x _ _ _ _ |- _ ] => 
    let h := Control.hyp h in invc $h
  | [ h : ?_x _ _ _ _ _ = ?_x _ _ _ _ _ |- _ ] => 
    let h := Control.hyp h in invc $h
  | [ h : ?_x _ _ _ _ _ _ = ?_x _ _ _ _ _ _ |- _ ] => 
    let h := Control.hyp h in invc $h
  end.

Ltac2 Notation find_inversion := find_inversion.

(** [prove_eq] derives equalities of arguments from an equality of
    constructed values. *)
Ltac2 Notation "prove_eq" :=
  match! goal with
  | [ h : ?_x ?x1 = ?_x ?y1 |- _ ] =>
    assert ($x1 = $y1) by congruence; 
    clear $h
  | [ h : ?_x ?x1 ?x2 = ?_x ?y1 ?y2 |- _ ] =>
    assert ($x1 = $y1) by congruence;
    assert ($x2 = $y2) by congruence;
    clear $h
  | [ h : ?_x ?x1 ?x2 ?x3 = ?_x ?y1 ?y2 ?y3 |- _ ] =>
    assert ($x1 = $y1) by congruence;
    assert ($x2 = $y2) by congruence;
    assert ($x3 = $y3) by congruence;
    clear $h
  end.

(** [break_let] breaks a destructuring [let] for a pair. *)
Ltac2 Notation "break_let" :=
  match! goal with
  | [ _h : context [ (let (_,_) := ?x in _) ] |- _ ] => 
    destruct $x eqn:?
  | [ |- context [ (let (_,_) := ?x in _) ] ] => 
    destruct $x eqn:?
  end.

Ltac2 Notation break_let := break_let.

(** [break_or_hyp] breaks a disjunctive hypothesis, splitting your
    goal into two. *)
Ltac2 Notation "break_or_hyp" :=
  match! goal with
  | [ h : _ \/ _ |- _ ] => 
    let h := Control.hyp h in invc $h
  end.
Ltac2 Notation break_or_hyp := break_or_hyp.

(** [copy_apply lem H] adds a hypothesis obtained by [apply]-ing [lem]
    in [H]. *)
Ltac copy_apply lem H :=
  let x := fresh in
  pose proof H as x;
    apply lem in x.

(** [copy_eapply lem H] adds a hypothesis obtained by [eapply]-ing
    [lem] in [H]. *)
Ltac copy_eapply lem H :=
  let x := fresh in
  pose proof H as x;
    eapply lem in x.

(** [conclude_using tac] specializes a hypothesis if it can prove its
    premise using [tac]. *)
Ltac conclude_using tac :=
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H tac
  end.

(** [find_higher_order_rewrite] tries to [rewrite] with
    possibly-quantified hypotheses into other hypotheses or the
    goal. *)
Ltac find_higher_order_rewrite :=
  match goal with
    | [ H : _ = _ |- _ ] => rewrite H in *
    | [ H : forall _, _ = _ |- _ ] => rewrite H in *
    | [ H : forall _ _, _ = _ |- _ ] => rewrite H in *
  end.

(** [find_reverse_higher_order_rewrite] tries to [rewrite <-] with
    possibly-quantified hypotheses into other hypotheses or the
    goal. *)
Ltac find_reverse_higher_order_rewrite :=
  match goal with
    | [ H : _ = _ |- _ ] => rewrite <- H in *
    | [ H : forall _, _ = _ |- _ ] => rewrite <- H in *
    | [ H : forall _ _, _ = _ |- _ ] => rewrite <- H in *
  end.

(** [find_apply_hyp_goal] tries solving the goal applying some
    hypothesis. *)
Ltac find_apply_hyp_goal :=
  match goal with
    | [ H : _ |- _ ] => solve [apply H]
  end.

(** [find_copy_apply_lem_hyp lem] tries to find a hypothesis to which
    [lem] can be applied, and adds a hypothesis resulting from the
    application. *)
Ltac find_copy_apply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => copy_apply lem H
  end.

(** [find_apply_hyp_hyp] finds a hypothesis which can be applied in
    another hypothesis, and performs the application. *)
Ltac find_apply_hyp_hyp :=
  match goal with
    | [ H : forall _, _ -> _,
        H' : _ |- _ ] =>
      apply H in H'; [idtac]
    | [ H : _ -> _ , H' : _ |- _ ] =>
      apply H in H'; auto; [idtac]
  end.

Ltac find_eapply_hyp_hyp :=
  match goal with
  | [ H : forall _, _ -> _,
        H' : _ |- _ ] =>
    eapply H in H'; [idtac]
  | [ H : _ -> _ , H' : _ |- _ ] =>
    eapply H in H'; auto; [idtac]
  end.

(** [find_copy_apply_hyp_hyp] finds a hypothesis which can be applied
    in another hypothesis, and adds a hypothesis with the application
    performed. *)
Ltac find_copy_apply_hyp_hyp :=
  match goal with
    | [ H : forall _, _ -> _,
        H' : _ |- _ ] =>
      copy_apply H H'; [idtac]
    | [ H : _ -> _ , H' : _ |- _ ] =>
      copy_apply H H'; auto; [idtac]
  end.

(** [find_apply_lem_hyp lem] finds a hypothesis where [lem] can be
    [apply]-ed, and performes the application. *)
Ltac find_apply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => apply lem in H
  end.

(** [find_eapply_lem_hyp lem] finds a hypothesis where [lem] can be
    [eapply]-ed, and performes the application. *)
Ltac find_eapply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => eapply lem in H
  end.

(** TODO: document this. *)
Ltac insterU H :=
  match type of H with
    | forall _ : ?T, _ =>
      let x := fresh "x" in
      evar (x : T);
      let x' := (eval unfold x in x) in
        clear x; specialize (H x')
  end.

(** TODO: document this. *)
Ltac find_insterU :=
  match goal with
    | [ H : forall _, _ |- _ ] => insterU H
  end.

(** [eapply_prop P] finds a hypothesis proving [P] and [eapply]-es it. *)
Ltac eapply_prop P :=
  match goal with
    | H : P _ |- _ =>
      eapply H
  end.

(** [find_eapply_prop P] finds a hypothesis including [P] and [eapply]-es it. *)
Ltac find_eapply_prop P :=
  match goal with
    | H : context [ P ] |- _ =>
      eapply H
  end.

(** [isVar t] succeeds if term [t] is a variable in the context. *)
Ltac isVar t :=
    match goal with
      | v : _ |- _ =>
        match t with
          | v => idtac
        end
    end.

(** [remGen t] is useful when one wants to do induction on a
    hypothesis whose indices are not concrete.  By default, the
    [induction] tactic will first generalize them, losing information
    in the process.  By introducing an equality, one can save this
    information while generalizing the hypothesis. *)
Ltac remGen t :=
  let x := fresh in
  let H := fresh in
  remember t as x eqn:H;
    generalize dependent H.

(** [remGenIfNotVar t] performs [remGen t] unless [t] is a simple
    variable. *)
Ltac remGenIfNotVar t := first [isVar t| remGen t].

(** [rememberNonVars H] will pose an equation for all indices of [H]
    that are concrete.  For instance, given: [H : P a (S b) c], it
    will generalize into [H : P a b' c] and [EQb : b' = S b]. *)
Ltac rememberNonVars H :=
  match type of H with
    | _ ?a ?b ?c ?d ?e =>
      remGenIfNotVar a;
      remGenIfNotVar b;
      remGenIfNotVar c;
      remGenIfNotVar d;
      remGenIfNotVar e
    | _ ?a ?b ?c ?d =>
      remGenIfNotVar a;
      remGenIfNotVar b;
      remGenIfNotVar c;
      remGenIfNotVar d
    | _ ?a ?b ?c =>
      remGenIfNotVar a;
      remGenIfNotVar b;
      remGenIfNotVar c
    | _ ?a ?b =>
      remGenIfNotVar a;
      remGenIfNotVar b
    | _ ?a =>
      remGenIfNotVar a
  end.

(* [generalizeEverythingElse H] tries to generalize everything that is
   not [H]. *)
Ltac generalizeEverythingElse H :=
  repeat match goal with
           | [ x : ?T |- _ ] =>
             first [
                 match H with
                   | x => fail 2
                 end |
                 match type of H with
                   | context [x] => fail 2
                 end |
                 revert x]
         end.

(* [prep_induction H] prepares your goal to perform [induction] on [H] by:
   - remembering all concrete indices of [H] via equations;
   - generalizing all variables that are not depending on [H] to strengthen the
     induction hypothesis. *)
Ltac prep_induction H :=
  rememberNonVars H;
  generalizeEverythingElse H.

(* [econcludes] tries to specialize a hypothesis using [eauto]. *)
Ltac econcludes :=
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H eauto
  end.

(** [find_copy_eapply_lem_hyp lem] tries to find a hypothesis to which
    [lem] can be [eapply]-ed, and adds a hypothesis resulting from the
    application. *)
Ltac find_copy_eapply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => copy_eapply lem H
  end.

(** [apply_prop_hyp P Q] tries to [apply] a hypothesis about [P] to a
    hypothesis about [Q]. *)
Ltac apply_prop_hyp P Q :=
  match goal with
  | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
    apply H in H'
  end.

(** [apply_prop_hyp P Q] tries to [eapply] a hypothesis about [P] to a
    hypothesis about [Q]. *)
Ltac eapply_prop_hyp P Q :=
  match goal with
  | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
    eapply H in H'
  end.

(** [apply_prop_hyp P Q] tries to [eapply] a hypothesis about [P] to a
    hypothesis about [Q], posing the result as a new hypothesis. *)
Ltac copy_eapply_prop_hyp P Q :=
  match goal with
    | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
      copy_eapply H H'
  end.

Ltac eapply_lem_prop_hyp lem P :=
  match goal with
  | [ H : context [ P ] |- _ ] =>
    eapply lem in H
  end.

Ltac copy_eapply_lem_prop_hyp lem P :=
  match goal with
  | [ H : context [ P ] |- _ ] =>
    copy_eapply lem H
  end.

(** [find_false] finds a hypothesis of the shape [P -> False] in the
    context and cuts your goal with it, leaving you with the
    obligation of proving its premise [P]. *)
Ltac find_false :=
  match goal with
    | H : _ -> False |- _ => exfalso; apply H
  end.

(** [injc H] performs [injection] on [H], then clears [H] and
    simplifies the context. *)
Ltac injc H :=
  injection H; clear H; intros; subst_max.

(** [find_injection] looks for an [injection] in the context and
    performs [injc]. *)
Ltac find_injection :=
  match goal with
    | [ H : ?X _ _ _ _ _ _ _ = ?X _ _ _ _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ _ _ _ = ?X _ _ _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ _ _ = ?X _ _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ _ = ?X _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ = ?X _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ = ?X _ _ |- _ ] => injc H
    | [ H : ?X _ = ?X _ |- _ ] => injc H
  end.

(** [aggressive_rewrite_goal] rewrites in the goal with any
    hypothesis. *)
Ltac aggressive_rewrite_goal :=
  match goal with H : _ |- _ => rewrite H end.

(** [break_exists_name x] destructs an existential in context and
    names the witness [x]. *)
Ltac break_exists_name x :=
  match goal with
  | [ H : exists _, _ |- _ ] => destruct H as [x H]
  end.

Tactic Notation "check_num_goals" natural(n) :=
  let num := numgoals in
  guard num = n.

Tactic Notation "check_num_goals_le" natural(n) :=
  let num := numgoals in
  guard num <= n.

Ltac break_logic_hyps :=
  repeat (
    try break_or_hyp;
    try break_and;
    try break_exists
  ).

Ltac break_iff :=
  match goal with
  | |- _ <-> _ => split; intros
  end.

Ltac full_do_bool :=
  intros; break_logic_hyps;
  do_bool;
  (* Do bool from extlib does well on hyps, but not goals *)
  repeat 
    (match goal with
    | |- context [andb ?x ?y = true] => 
      erewrite andb_true_iff; split; do_bool
    | |- context [andb ?x ?y = false] => 
      erewrite andb_false_iff; split; do_bool
    | |- context [orb ?x ?y = true] => 
      erewrite orb_true_iff; do_bool; eauto
    | |- context [orb ?x ?y = false] => 
      erewrite orb_false_iff; do_bool; eauto
    end; try simple congruence 1);
  try simple congruence 1.

Ltac max_RW :=
  simpl in *;
  subst_max;
  repeat find_rewrite.

Ltac breaker :=
  repeat (break_match; subst; try congruence).

Ltac rw_all :=
  subst_max;
  repeat (
    match goal with
    | H : context [iff _ _] , H' : _ |- _ => 
      erewrite H in H'
    | H : context [eq _ _] , H' : _ |- _ => 
      erewrite H in H'
    | H : context [iff _ _] |- _ => 
      erewrite H
    | H : context [eq _ _] |- _ =>
      erewrite H
    end;
    subst_max;
    eauto;
    try simple congruence 1
  ); eauto.

Ltac2 tac_list_thunk tac_list :=
  match tac_list with
  | None => fun () => ()
  | Some tacs => 
      List.fold_left 
        (fun acc x => (fun next => acc (); x (); next)) 
        (fun () => ()) 
        tacs
  end.

(* Simplification hammer.  Used at beginning of many proofs in this 
   development.  Conservative simplification, break matches, 
   invert on resulting goals *)
Ltac2 rec ff tac :=
  repeat (
    ltac1:(try unfold not in *;
    intros;
    (* Break up logical statements *)
    repeat break_and;
    repeat break_exists;
    try break_iff);
    (* 
    This is proving too computationly expensive to do in general
    *)
    try (tac ());
    ltac1:(repeat (
      simpl in *;
      repeat find_rewrite;
      try break_match;
      try congruence;
      repeat find_rewrite;
      try congruence;
      repeat find_injection;
      try congruence;
      simpl in *;
      subst_max; eauto;
      try congruence
      (* Too expensive in general
      ; try solve_by_inversion *)
    ));
    (* We only break up hyp ORs if we <= the total number of goals *)
    try (
      let num := numgoals () in
      ltac1:(break_or_hyp); ff tac; 
      ltac1:(num |- let num2 := numgoals in
      guard num2 <= num) (Ltac1.of_int num))
  ).

Ltac2 l := fun _ => ltac1:(try lia).
Ltac2 Notation "l" := l.
Ltac2 u := fun _ => ltac1:(repeat autounfold in *).
Ltac2 Notation "u" := u.
Ltac2 a := fun _ => ltac1:(repeat find_apply_hyp_hyp).
Ltac2 Notation "a" := a.
Ltac2 r := fun _ => ltac1:(rw_all).
Ltac2 Notation "r" := r.
Ltac2 v := fun _ => ltac1:(vm_compute).
Ltac2 Notation "v" := v.
Ltac2 d := fun _ => ltac1:(idtac "DebugPrint").
Ltac2 Notation "d" := d.

(* [interp_tac_str] interprets a string as a sequence of tactics. *)

Ltac2 ff_core tac_list :=
  let tac := tac_list_thunk tac_list in
  repeat (
    ff tac;
    tac ();
    ff tac
  ).

Ltac2 Notation "ff" 
  tacs(opt(list0(tactic(0), ","))) :=
  ff_core tacs.

Ltac target_find_rewrite H :=
  lazymatch type of H with
  | ?X = ?Y =>
    (* rewrite in goals *)
    lazymatch goal with
    | [ |- context[X] ] => rewrite H
    end;
    (* rewrite in hyps *)
    lazymatch goal with
    | [ H' : context[X] |- _ ] => 
      rewrite H in H'; clear H
    end
  end.

Ltac clean_up_hyp H :=
  (* try injc H;
  try target_find_rewrite H; *)
  try simple congruence 1.

Ltac target_break_match H :=
  lazymatch type of H with
  | context[match ?X with _ => _ end] => 
    let Hbm := fresh "Hbm" in
    destruct X eqn:Hbm; 
    try find_injection;
    try simple congruence 1; try target_break_match Hbm;
    try target_break_match H
  end.

Ltac2 pose_proof (x : constr) (y : ident option) :=
  match y with
  | None => ltac1:(x |- pose proof x) (Ltac1.of_constr x)
  | Some yval =>
    ltac1:(x y |- pose proof x as y) (Ltac1.of_constr x) (Ltac1.of_ident yval)
  end.

Ltac2 Notation "pose" "proof" 
  x(constr)
  y(opt(seq("as", ident))) :=
  pose_proof x y.

Ltac2 Notation "pp"
  x(constr)
  y(opt(seq("as", ident))) :=
  pose_proof x y.

Ltac2 Notation "pps" 
  xs(list0(constr, ",")) :=
  List.fold_left (fun _ x => pose_proof x None) () xs.