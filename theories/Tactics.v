(* Local copy of structural tactics library from:  https://github.com/uwplse/StructTact 

We have locally modified this a great deal to add tactics that are useful for our proofs. *)
From Stdlib Require Import Bool String List Ascii Lia.
Import ListNotations.

From Ltac2 Require Export Ltac2 Printf Pstring Notations.
From Ltac2 Require Export Bool Lazy Array Lazy FMap Fresh Control Ltac1 Constr.

Ltac2 dump_hyps () :=
  let hyps := Control.hyps () in
  List.iter 
    (fun (var, val, ty) => 
      match val with
      | Some v => 
        printf "%I := %t = %t" var v ty
      | None =>
        printf "%I : %t" var ty
      end)
    hyps.

Ltac2 dump_goal () :=
  let goal := Control.goal () in
  printf "%t" goal.

(** [dump] prints out the current goal and context. *)

(** [dump_state] prints out the current goal and context. *)

(* Prints out the current state*)
Ltac2 dump_state () :=
  (* Dump it for all hyps *)
  printf "========================";
  printf "Dumping State";
  printf "========================";
  Control.enter (fun () => 
    printf "========================";
    dump_hyps ();
    printf "------------------------";
    dump_goal ();
    printf "========================"
  ).
Ltac2 Notation "dump_state" := dump_state ().
Ltac2 Notation dump := dump_state.

Ltac2 Notation tac1(thunk(self)) "|||" tac2(thunk(self)) : 6 :=
  orelse
    (fun () =>
        (* Attempt to run the first tactic *)
        tac1 ()
    )
    (fun (_e : exn) =>
        (* If the first tactic fails, run the second one *)
        tac2 ()
    ).

Ltac2 can_pretype (ptm : preterm) : constr option :=
  ((* Attempt to pretype using flags that disallow new evar creation.
      Pretype.Flags.constr_flags has 'allow_evars' set to false by default. *)
    Some (Pretype.pretype Pretype.Flags.constr_flags Pretype.expected_without_type_constraint ptm)
  ) ||| None.

Ltac2 Notation "?!" opt_val(tactic(0)) :=
  match opt_val with
  | Some _ => true
  | None => false
  end.

Example test_notation_and_can_pretype :
  forall A (x y : A), True.
Proof.
  intros.
  if (?! (can_pretype preterm:(x <> z)))
  then fail
  else apply I.
Qed.

(** [already_proven h] returns a boolean value on if the hypothesis "h" is already in the current hypotheses *)
Ltac2 already_proven (h : preterm) : bool :=
  (* first, we try to pretype it, if that fails, then obviously it doesn't already exist *)
  match can_pretype h with
  | Some h' =>
    (* If we can pretype it, then we check if it exists in the current hypotheses *)
    List.exist (fun (_, _, ty) => Constr.equal h' ty) (Control.hyps ())
  | None =>
    (* If we can't pretype it, then we check if it exists in the current hypotheses *)
    false
  end.

Example test_already_proven : forall A (x y : A), x = y -> True.
Proof.
  intros.
  if (already_proven preterm:(x = y))
  then apply I
  else fail.
Qed.

(** [already_proven_hyp h] returns a boolean value on if the hypothesis "h" is already in the current hypotheses *)

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
Ltac inv H := inversion H; ltac2:(subst_max).
Ltac2 Notation "inv" arg(ident) := ltac1:(H |- inv H) (Ltac1.of_ident arg).

Example test_inv : forall A (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros.
  inv H.
  reflexivity.
Qed.

Ltac2 Notation "invc" arg(ident) := 
  ltac1:(H |- inv H) (Ltac1.of_ident arg); 
  clear $arg.

Ltac2 Notation "invcs" arg(ident) := 
  ltac1:(H |- inv H) (Ltac1.of_ident arg);
  clear $arg; simpl in *.

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
Ltac2 Notation break_match := break_match.

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
  | [ h : ?_x _ = ?_x _ |- _ ] => invc $h
  | [ h : ?_x _ _ = ?_x _ _ |- _ ] => invc $h
  | [ h : ?_x _ _ _ = ?_x _ _ _ |- _ ] => invc $h
  | [ h : ?_x _ _ _ _ = ?_x _ _ _ _ |- _ ] => invc $h
  | [ h : ?_x _ _ _ _ _ = ?_x _ _ _ _ _ |- _ ] => invc $h
  | [ h : ?_x _ _ _ _ _ _ = ?_x _ _ _ _ _ _ |- _ ] => invc $h
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
  | [ h : _ \/ _ |- _ ] => invc $h
  end.
Ltac2 Notation break_or_hyp := break_or_hyp.

(** [find_higher_order_rewrite] tries to [rewrite] with
    possibly-quantified hypotheses into other hypotheses or the
    goal. *)
Ltac2 Notation "find_higher_order_rewrite" :=
  Control.enter (
  fun () =>
  match! goal with
  | [ h : _ = _ |- _ ] => 
    let h := Control.hyp h in rewrite $h in *
  | [ h : forall _, _ = _ |- _ ] => 
    let h := Control.hyp h in rewrite $h in *
  | [ h : forall _ _, _ = _ |- _ ] => 
    let h := Control.hyp h in rewrite $h in *
  end).

Ltac2 Notation find_higher_order_rewrite := find_higher_order_rewrite.

(** [find_reverse_higher_order_rewrite] tries to [rewrite <-] with
    possibly-quantified hypotheses into other hypotheses or the
    goal. *)
Ltac2 Notation "find_reverse_higher_order_rewrite" :=
  Control.enter (
  fun () =>
  match! goal with
  | [ h : _ = _ |- _ ] => 
    let h := Control.hyp h in rewrite <- $h in *
  | [ h : forall _, _ = _ |- _ ] => 
    let h := Control.hyp h in rewrite <- $h in *
  | [ h : forall _ _, _ = _ |- _ ] =>
    let h := Control.hyp h in rewrite <- $h in *
  end).

Ltac2 Notation find_reverse_higher_order_rewrite := find_reverse_higher_order_rewrite.

(** [find_apply_hyp_goal] tries solving the goal applying some
    hypothesis. *)
Ltac2 Notation "find_apply_hyp_goal" :=
  match! goal with
  | [ h : _ |- _ ] => 
    let h := Control.hyp h in
    solve [apply $h]
  end.

(** [find_apply_hyp_hyp] finds a hypothesis which can be applied in
    another hypothesis, and performs the application. *)
Ltac2 Notation "find_apply_hyp_hyp" :=
  Control.enter (
  fun () =>
  match! goal with
  | [ h : forall _, _ -> _,
      h' : _ |- _ ] =>
    let h := Control.hyp h in
    apply $h in $h' > [()]
  | [ h : _ -> _ , 
      h' : _ |- _ ] =>
    let h := Control.hyp h in
    apply $h in $h'; eauto > [()]
  end).

Ltac2 Notation find_apply_hyp_hyp := find_apply_hyp_hyp.

Ltac2 Notation "find_eapply_hyp_hyp" :=
  Control.enter (
  fun () =>
  match! goal with
  | [ h : forall _, _ -> _,
      h' : _ |- _ ] =>
    let h := Control.hyp h in
    eapply $h in $h' > [()]
  | [ h : _ -> _ , 
      h' : _ |- _ ] =>
    let h := Control.hyp h in
    eapply $h in $h'; eauto > [()]
  end).

Ltac2 Notation find_eapply_hyp_hyp := find_eapply_hyp_hyp.

(** [find_eapply_lem_hyp lem] finds a hypothesis where [lem] can be
    [eapply]-ed, and performes the application. *)
Ltac2 Notation "find_eapply_lem_hyp" 
  lem(open_constr) :=
  Control.enter (
  fun () =>
  match! goal with
  | [ h : _ |- _ ] => 
    eapply $lem in $h
  end).

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

Ltac2 Notation "prep_induction" 
  h(ident) :=
  ltac1:(h |- prep_induction h) (Ltac1.of_ident h).

(** [injc H] performs [injection] on [H], then clears [H] and
    simplifies the context. *)
Ltac2 injc (h : ident) :=
  ltac1:(h |- injection h) (Ltac1.of_ident h);
  clear h; intros; subst_max.

(** [find_injection] looks for an [injection] in the context and
    performs [injc]. *)
Ltac2 Notation "find_injection" :=
  match! goal with
  | [ h : ?_x _ = ?_x _ |- _ ] => injc h
  | [ h : ?_x _ _ = ?_x _ _ |- _ ] => injc h
  | [ h : ?_x _ _ _ = ?_x _ _ _ |- _ ] => injc h
  | [ h : ?_x _ _ _ _ = ?_x _ _ _ _ |- _ ] => injc h
  | [ h : ?_x _ _ _ _ _ = ?_x _ _ _ _ _ |- _ ] => injc h
  | [ h : ?_x _ _ _ _ _ _ = ?_x _ _ _ _ _ _ |- _ ] => injc h
  | [ h : ?_x _ _ _ _ _ _ _ = ?_x _ _ _ _ _ _ _ |- _ ] => injc h
  end.
Ltac2 Notation find_injection := find_injection.

(** [aggressive_rewrite_goal] rewrites in the goal with any
    hypothesis. *)
Ltac2 Notation "aggressive_rewrite_goal" :=
  match! goal with 
  | [ h : _ |- _ ] => 
    let h := Control.hyp h in
    rewrite $h
  end.

Ltac2 Notation "break_logic_hyps" :=
  repeat (
    try break_or_hyp;
    try break_and;
    try break_exists
  ).

Ltac2 Notation "break_iff" :=
  match! goal with
  | [ |- _ <-> _ ] => split; intros
  end.

Ltac2 Notation break_iff := break_iff.

Ltac2 Notation "do_bool" :=
  intros; break_logic_hyps;
  (* Unfold all the bool notations *)
  repeat 
    (match! goal with
    (* Match hyps *)
    | [ h : context [andb ?_x ?_y = true] |- _ ] => 
      erewrite andb_true_iff in $h; 
      let h := Control.hyp h in
      destruct $h; eauto
    | [ h : context [andb ?_x ?_y = false] |- _ ] => 
      erewrite andb_false_iff in $h; 
      let h := Control.hyp h in
      destruct $h; eauto
    | [ h : context [orb ?_x ?_y = true] |- _ ] => 
      erewrite orb_true_iff in $h; 
      let h := Control.hyp h in
      destruct $h; eauto
    | [ h : context [orb ?_x ?_y = false] |- _ ] => 
      erewrite orb_false_iff in $h; 
      let h := Control.hyp h in
      destruct $h; eauto
    (* Match goal *)
    | [ |- context [andb ?_x ?_y = true] ] => 
      erewrite andb_true_iff; split; eauto
    | [ |- context [andb ?_x ?_y = false] ] => 
      erewrite andb_false_iff; split; eauto
    | [ |- context [orb ?_x ?_y = true] ] => 
      erewrite orb_true_iff; eauto
    | [ |- context [orb ?_x ?_y = false] ] => 
      erewrite orb_false_iff; eauto
    end; try (simple congruence 1));
  try (simple congruence 1).

Example test_do_bool : forall x y z : bool,
  ((x && y) || z) = true -> (x = true /\ y = true) \/ z = true.
Proof.
  do_bool.
Qed.

Ltac2 Notation max_RW :=
  simpl in *;
  subst_max;
  repeat find_rewrite.

Ltac2 Notation breaker :=
  repeat (
    break_match; 
    subst; 
    try (congruence)
  ).

Ltac2 Notation "rw_all" :=
  subst_max;
  repeat (
    match! goal with
    | [ h : context [iff _ _], 
        h' : _ |- _] => 
      let h := Control.hyp h in
      erewrite $h in $h'
    | [ h : context [eq _ _] , 
        h' : _ |- _] => 
      let h := Control.hyp h in
      erewrite $h in $h'
    | [ h : context [iff _ _] |- _ ] => 
      let h := Control.hyp h in
      erewrite $h
    | [ h : context [eq _ _] |- _ ] =>
      let h := Control.hyp h in
      erewrite $h
    end;
    subst_max;
    eauto;
    try (simple congruence 1)
  ); eauto.

Ltac2 Notation rw_all := rw_all.

Ltac2 tac_list_thunk tac_list :=
  match tac_list with
  | None => fun () => ()
  | Some tacs => 
      List.fold_left 
        (fun acc x => (fun next => acc (); x (); next)) 
        (fun () => ()) 
        tacs
  end.

Ltac2 Notation "find_contra" :=
  match! goal with
  | [ h : False |- _ ] =>
    ltac1:(h |- exfalso; exact h) (Ltac1.of_ident h)
  end |||
  (match! goal with
  | [ |- { _ } + { _ } ] =>
    right; intros;
    try (intros ?); congruence
  end).
Ltac2 Notation find_contra := find_contra.

(* Simplification hammer.  Used at beginning of many proofs in this 
   development.  Conservative simplification, break matches, 
   invert on resulting goals *)
Ltac2 rec ff tac :=
  repeat (
    try (unfold not in *);
    intros;
    (* Break up logical statements *)
    repeat break_and;
    repeat break_exists;
    try break_iff;
    (* 
    This is proving too computationly expensive to do in general
    *)
    try (tac ());
    repeat (
      simpl in *;
      repeat find_rewrite;
      try break_match;
      try (congruence);
      repeat find_rewrite;
      try (congruence);
      repeat (find_injection);
      try (congruence);
      simpl in *;
      subst_max; eauto;
      try (congruence);
      try (find_contra)
      (* Too expensive in general
      ; try solve_by_inversion *)
    );
    (* We only break up hyp ORs if we <= the total number of goals *)
    try (
      let num := numgoals () in
      break_or_hyp; ff tac; 
      ltac1:(num |- let num2 := numgoals in
      guard num2 <= num) (Ltac1.of_int num))
  ).

Ltac2 Notation "lia" := 
  ltac1:(lia).
Ltac2 Notation lia := lia.

Ltac2 l := fun _ => try lia.
Ltac2 Notation "l" := l.
Ltac2 u := fun _ => ltac1:(repeat autounfold in *).
Ltac2 Notation "u" := u.
Ltac2 a := fun _ => repeat find_apply_hyp_hyp.
Ltac2 Notation "a" := a.
Ltac2 r := fun _ => rw_all.
Ltac2 Notation "r" := r.
Ltac2 v := fun _ => vm_compute.
Ltac2 Notation "v" := v.
Ltac2 d := fun _ => printf "DebugPrint".
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
  tacs(opt(list0(tactic(0), ","))) 
  :=
  (* Default timeout of 30 seconds *)
  Control.timeout 30 (fun () => ff_core tacs).

Ltac2 rec target_break_match
  (h : ident) :=
  lazy_match! Constr.type (Control.hyp h)with
  | context[match ?x with _ => _ end] => 
    let h' := Fresh.in_goal h in
    destruct $x eqn:$h'; 
    try (find_injection);
    try (simple congruence 1); 
    try (target_break_match h');
    try (target_break_match h)
  end.

Ltac2 pose_proof (x : constr) (y : ident option) :=
  match y with
  | None => ltac1:(x |- pose proof x) (Ltac1.of_constr x)
  | Some yval =>
    ltac1:(x y |- pose proof x as y) (Ltac1.of_constr x) (Ltac1.of_ident yval)
  end.

(*  
----------------------------------------------
My semi-compatability layer for Ltac1 -> Ltac2
----------------------------------------------
*)

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

Ltac2 Notation "ref" x(preterm) :=
  ltac1:(x |- refine x) (Ltac1.of_preterm x).

Ltac2 Notation congruence := congruence.
Ltac2 Notation cong := congruence.

Ltac2 Notation "intuition" := ltac1:(intuition).
Ltac2 Notation intuition := intuition.

Ltac2 Notation "ar"
  dbs(opt(seq("with", hintdb)))
  cl(opt(clause))
  tac(opt(seq("by", thunk(tactic))))
  :=
  let db := default_list (default_db dbs) in
  let cl := default_on_concl cl in
  try (Std.autorewrite true tac db cl).


(**
 * [fresh_names_in_goal n basename] generates a list of [n] fresh identifiers
 * that do not conflict with names currently in the goal or with each other.
 * All generated names will have [basename] as their prefix.
 *)
Ltac2 rec fresh_names_in_goal (n : int) (basename : ident) (avoid : Fresh.Free.t) (acc : ident list) : ident list :=
  if Int.le n 0 then
    List.rev acc
  else
    let h := Fresh.fresh avoid basename in
    fresh_names_in_goal (Int.sub n 1) basename 
      (Free.union (Free.of_ids [h]) avoid) (h :: acc).

(**
 * A convenient wrapper to generate a list of [n] fresh hypothesis names.
 *)
Ltac2 fresh_hyps (n : int) (basename : string) : ident list :=
  match Ident.of_string basename with
  | None => throw_invalid_argument "fresh_hyps" "basename must be a valid identifier"
  | Some name =>
    (* Generate fresh names in the goal, avoiding conflicts with existing names *)
    fresh_names_in_goal n name (Fresh.Free.of_goal ()) []
  end.

(**
 * A variant of [fresh_hyp] that always generates a single fresh name.
 *)
Ltac2 fresh_hyp (basename : string) : ident :=
  let avoid := Fresh.Free.of_goal () in
  match Ident.of_string basename with
  | None => throw_invalid_argument "fresh_hyp" "basename must be a valid identifier"
  | Some basename_ident =>
    (* Generate a single fresh name, avoiding conflicts with existing names *)
    Fresh.fresh avoid basename_ident
  end.