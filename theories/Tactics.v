(* Local copy of structural tactics library from:  https://github.com/uwplse/StructTact 

We have locally modified this a great deal to add tactics that are useful for our proofs. *)
From Stdlib Require Export Bool Nat String List Ascii Lia.
Import ListNotations.

From Ltac2 Require Export Ltac2 Printf Pstring Notations.
From Ltac2 Require Export Bool Lazy Array Lazy FMap Fresh Control Ltac1 Constr.

(* Helper to generate indentation string *)
Ltac2 rec make_indent (n : int) : string :=
  if Int.equal n 0 then "" 
  else String.concat "" ["  "; make_indent (Int.sub n 1)].

Ltac2 rec print_unsafe_aux (indent : int) (t : constr) : unit :=
  let ind := make_indent indent in
  
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Rel n => 
      printf "%s(Rel %i)" ind n

  | Constr.Unsafe.Var id => 
      printf "%s(Var %I)" ind id

  | Constr.Unsafe.Meta _ => 
      (* Ignoring the variable part as requested *)
      printf "%s(Meta)" ind

  | Constr.Unsafe.Evar _ args => 
      (* Ignoring the EvarKey, just showing it has children *)
      printf "%s(Evar" ind;
      Array.iter (print_unsafe_aux (Int.add indent 1)) args;
      printf "%s)" ind

  | Constr.Unsafe.Sort _ => 
      printf "%s(Sort)" ind

  | Constr.Unsafe.Cast c _ ty => 
      printf "%s(Cast" ind;
      print_unsafe_aux (Int.add indent 1) c;
      print_unsafe_aux (Int.add indent 1) ty;
      printf "%s)" ind

  | Constr.Unsafe.Prod b body => 
      let name := match Constr.Binder.name b with 
                  | Some i => Ident.to_string i 
                  | None => "_" 
                  end in
      (* Construct the header string to ensure it prints on one line *)
      printf "%s(Prod %s :" ind name;
      print_unsafe_aux (Int.add indent 1) (Constr.Binder.type b);
      print_unsafe_aux (Int.add indent 1) body;
      printf "%s)" ind

  | Constr.Unsafe.Lambda b body => 
      let name := match Constr.Binder.name b with 
                  | Some i => Ident.to_string i 
                  | None => "_" 
                  end in
      printf "%s(Lambda %s :" ind name;
      print_unsafe_aux (Int.add indent 1) (Constr.Binder.type b);
      print_unsafe_aux (Int.add indent 1) body;
      printf "%s)" ind

  | Constr.Unsafe.LetIn b val body => 
      let name := match Constr.Binder.name b with 
                  | Some i => Ident.to_string i 
                  | None => "_" 
                  end in
      printf "%s(LetIn %s :=" ind name;
      print_unsafe_aux (Int.add indent 1) val;
      print_unsafe_aux (Int.add indent 1) (Constr.Binder.type b);
      print_unsafe_aux (Int.add indent 1) body;
      printf "%s)" ind

  | Constr.Unsafe.App f args => 
      printf "%s(App" ind;
      print_unsafe_aux (Int.add indent 1) f;
      Array.iter (print_unsafe_aux (Int.add indent 1)) args;
      printf "%s)" ind

  | Constr.Unsafe.Constant _ _ => 
      (* Printing 't' here uses the pretty printer for the name (e.g. Nat.add) *)
      printf "%s(Constant %t)" ind t

  | Constr.Unsafe.Ind _ _ => 
      printf "%s(Ind %t)" ind t

  | Constr.Unsafe.Constructor _ _ => 
      printf "%s(Constructor %t)" ind t
      
  | _ => 
      printf "%s(Other)" ind
  end.

Ltac2 print_unsafe (t : constr) : unit :=
  print_unsafe_aux 0 t.

(* Compatability/Notational Layer *)
Ltac2 Notation "ref" x(preterm) :=
  ltac1:(x |- refine x) (Ltac1.of_preterm x).

Ltac2 Notation congruence := congruence.
Ltac2 Notation cong := congruence.

Ltac2 Notation "intuition" := ltac1:(intuition).
Ltac2 Notation intuition := intuition.

Ltac2 Notation "eassumption" := ltac1:(eassumption).
Ltac2 Notation eassumption := eassumption.

Ltac2 Notation "exfalso" := ltac1:(exfalso).
Ltac2 Notation exfalso := exfalso.

(*  
----------------------------------------------
My semi-compatability layer for Ltac1 -> Ltac2
----------------------------------------------
*)

Ltac2 pose_proof (x : constr) (y : ident option) :=
  Control.enter (fun () => 
  match y with
  | None => ltac1:(x |- pose proof x) (Ltac1.of_constr x)
  | Some yval =>
    ltac1:(x y |- pose proof x as y) (Ltac1.of_constr x) (Ltac1.of_ident yval)
  end).

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

Ltac2 Notation "clearbody" 
  ids(list1(ident)) :=
  Std.clearbody ids.

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

Ltac2 rec get_forall_var_names (h : constr) : ident list :=
  match! h with
  | forall _ : _, _ =>
    match Constr.Unsafe.kind h with
    | Unsafe.Prod bnd rst => 
      let rest : ident list := get_forall_var_names rst in
      match Binder.name bnd with
      | Some i => i :: rest
      | None => 
        match Ident.of_string "H" with
        | Some id => id :: rest
        | None => Control.zero (Tactic_failure None)
        end
      end
    | _ => Control.zero (Tactic_failure None)
    end
  | _ => []
  end.

Ltac2 get_forall_var_name (h : constr) : ident :=
  match get_forall_var_names h with
  | [] => Control.zero (Tactic_failure None)
  | x :: _ => x
  end.


Ltac2 Notation "rep" 
  t1(constr)
  t2(seq("with", constr))
  tac(opt(seq("by", thunk(tactic)))) 
  :=
  match tac with
  | None => 
    ltac1:(t1 t2 |- replace t1 with t2)
      (Ltac1.of_constr t1) 
      (Ltac1.of_constr t2) 
  | Some t' => 
    (ltac1:(t1 t2 |- replace t1 with t2) 
      (Ltac1.of_constr t1) 
      (Ltac1.of_constr t2)) > [ | solve [ t' () ] ]
  end.


(* Debugging Tools *)
Ltac2 guard_goals_le n :=
  let num := numgoals () in
  if (Int.le num n) then () else fail.

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

Ltac2 all_of_type (t : constr) :=
  List.fold_left
    (fun acc (var, _val, ty) =>
      if Constr.equal ty t
      then var :: acc
      else acc)
    []
    (Control.hyps ()).

Ltac2 all_of_type_filter (f : constr -> bool) :=
  List.fold_left
    (fun acc (var, _val, ty) =>
      if f ty
      then var :: acc
      else acc)
    []
    (Control.hyps ()).

Ltac2 apply_to_all_of_type
  (t : constr)
  (tac : ident -> unit) :=
  let vars := all_of_type t in
  List.iter (fun i => Control.enter (fun () => tac i)) vars.

Ltac2 apply_to_all_of_type_filter
  (f : constr -> bool)
  (tac : ident -> unit) :=
  let vars := all_of_type_filter f in
  List.iter (fun i => Control.enter (fun () => tac i)) vars.

Example test_all_of_type : forall A (x y : A) (p q : nat),
  x = y ->
  True.
Proof.
  intros.
  let a_s := all_of_type constr:(A) in
  let a_s_len := List.length a_s in
  if Int.equal a_s_len 2 then
    apply I
  else
    (printf "Expected 2 A's, found %i" a_s_len;
    fail).
Qed.

(* Helper: recursively dig into an application to find the head constructor. 
   Returns Some(term) if the head is a Constructor, otherwise None. *)
Ltac2 rec get_constructor_head (c : constr) : constr option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => Some c
  | Constr.Unsafe.App f _ => get_constructor_head f
  | _ => None
  end.

(* Check if a term is an equality between distinct constructors. 
   e.g. "true = false", "S n = 0", "cons x xs = nil" *)
Ltac2 is_discr_equality (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App head args =>
    (* Check if it is the '@eq' constant *)
    if Constr.equal head '(@eq) then
      (* args is [Type; lhs; rhs] *)
      if Int.equal (Array.length args) 3 
      then (
        let lhs := Array.get args 1 in
        let rhs := Array.get args 2 in
        match get_constructor_head lhs with
        | Some h1 =>
          match get_constructor_head rhs with
          | Some h2 => 
            (* If both are constructors, but NOT the same one, 
                then the equality is impossible. *)
            Bool.neg (Constr.equal h1 h2)
          | None => false
          end
        | None => false
        end
      )
      else false
    else false
  | _ => false
  end.

Example test_is_discr_equality_1 : forall n ns,
  true = false ->
  false = true ->
  true = true ->
  S n = 0 ->
  0 = S n ->
  0 = 0 ->
  cons n ns = nil ->
  nil = cons n ns ->
  @nil nat = nil ->
  ("x" = "")%string ->
  ("" = "x")%string ->
  ("" = "")%string ->
  True.
Proof.
  intros n ns Hb1 Hb2 HbG Hn1 Hn2 HnG Hl1 Hl2 HlG Hs1 Hs2 HsG.
  let gather h := Constr.type (Control.hyp h) in
  let tests := [
    is_discr_equality (gather ident:(Hb1));
    is_discr_equality (gather ident:(Hb2));
    neg (is_discr_equality (gather ident:(HbG)));
    is_discr_equality (gather ident:(Hn1));
    is_discr_equality (gather ident:(Hn2));
    neg (is_discr_equality (gather ident:(HnG)));
    is_discr_equality (gather ident:(Hl1));
    is_discr_equality (gather ident:(Hl2));
    neg (is_discr_equality (gather ident:(HlG)));
    is_discr_equality (gather ident:(Hs1));
    is_discr_equality (gather ident:(Hs2));
    neg (is_discr_equality (gather ident:(HsG)))
  ] in
  if (List.for_all (fun b => b) tests) 
  then apply I
  else fail.
Qed.

(* Check if 'c' is visibly False or 'Absurd = Absurd' *)
Ltac2 is_refutable (c : constr) : bool :=
  (* 1. Is it literally False? *)
  if Constr.equal c '(False) then true 
  else 
    (* 2. Is it a discriminable equality? *)
    if is_discr_equality c then true
    else 
      (* 3. Optional: Try shallow reduction to expose False *)
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.Ind _ _ => Constr.equal c '(False)
      | _ => false
      end.

Example test_is_refuable :
  False ->
  (0 = 1) ->
  True.
Proof.
  intros Hf Heq.
  let gather h := Constr.type (Control.hyp h) in
  let tests := [
    is_refutable (gather ident:(Hf));
    is_refutable (gather ident:(Heq))
  ] in
  if (List.for_all (fun b => b) tests) 
  then apply I
  else fail.
Qed.

(** [clean] removes any hypothesis of the shape [X = X]
    or [False -> _]

    It returns a list of the removed hypotheses.
*)
  (* Logic to identify reflexivity: x = x *)
Ltac2 is_reflexive (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App head args =>
      if Constr.equal head '(@eq) then
        match Array.length args with
        | 3 => Constr.equal (Array.get args 1) (Array.get args 2)
        | _ => false
        end
      else false
  | _ => false
  end.

Ltac2 clean_list (hs : (ident * constr option * constr) list) : ident list :=
  (* Logic to identify implications with a refutable domain *)
  let is_useless_implication (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Prod binder _body =>
        let domain := Constr.Binder.type binder in
        (* Avoiding any eval for now!
        (* Evaluate HNF to handle 'not True' -> 'True -> False' *)
        let domain := Std.eval_hnf domain in 
        *)
        is_refutable domain
    | _ => false
    end
  in
  let cleaners := 
    List.fold_left
      (fun acc (var, _val, ty) =>
        if (is_reflexive ty) || (is_useless_implication ty) 
        then var :: acc
        else acc)
      []
      hs
  in
  Std.clear cleaners;
  cleaners.

Ltac2 Notation "clean" := 
  Control.enter (fun () => 
    let _ := clean_list (Control.hyps ()) in
    ()
  ).

Example test_clean : forall A (x : A) P, 
  x = x -> 
  (False -> P) ->
  (0 = 1 -> P) ->
  True.
Proof.
  intros A x P Hx HfP HnP.
  clean.
  (* After cleaning, Hx, HfP and HnP should be removed *)
  let remaining_hyps := Control.hyps () in
  let remaining_names := List.map (fun (var, _, _) => var) remaining_hyps in
  if (
    List.exist (fun v => 
      (Ident.equal v ident:(Hx)) 
      || (Ident.equal v ident:(HfP)) 
      || (Ident.equal v ident:(HnP))
    ) 
    remaining_names
  )
  then fail
  else (apply I).
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
    (* TODO: Determine why this happens sometimes? I feel like subst should do this instead! *)
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
  lem(preterm) :=
  (* NOTE: We have to parse a preterm, then pretyp within an Enter. This is due to Ltac2's rejection of the possibility of the "lem" existing globally *)
  Control.enter (
  fun () =>
  match! goal with
  | [ h : _ |- _ ] => 
    let lem := Constr.pretype lem in
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

Ltac2 Notation "generalizeEverythingElse"
  h(ident) :=
  ltac1:(h |- generalizeEverythingElse h) (Ltac1.of_ident h).

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
  clear $h; intros; subst_max.

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


(* --- UTILITIES --- *)

(* Safely get a hypothesis, returning None if it was cleared/substed *)
Ltac2 safe_hyp (id : ident) 
    : (ident * constr option * constr) option :=
  match List.find_opt (fun (i, _, _) => Ident.equal i id) (Control.hyps ()) with
  | Some h => Some h
  | None => None
  end.

(* --- CORE AUTOMATION --- *)

Ltac2 is_constructor_app (c : constr) : constr option :=
  (* Returns the Head Constructor if the term is (C ...) *)
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => Some c
  | Constr.Unsafe.App head _ => 
      match Constr.Unsafe.kind head with
      | Constr.Unsafe.Constructor _ _ => Some head
      | _ => None
      end
  | _ => None
  end.

Ltac2 is_injectable_equality (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App head args =>
      if Constr.equal head '(@eq) then 
         (* eq A x y *)
         if Int.equal (Array.length args) 3 then
           let lhs := Array.get args 1 in
           let rhs := Array.get args 2 in
           match is_constructor_app lhs, is_constructor_app rhs with
           | Some c1, Some c2 => Constr.equal c1 c2 (* Same constructor? Injectable! *)
           | _, _ => false
           end
         else false
      else false
  | _ => false
  end.

(* Returns the list of NEW hypotheses created by injection *)
Ltac2 inject_and_subst (h : ident) : unit :=
  (* Perform injection and clear the original *)
  Std.injection 
    true 
    (Some [Std.IntroNaming Std.IntroAnonymous]) 
    (Some (Std.ElimOnIdent h));
  subst.

(* The destruct_match tactic. 
   Optimized to avoid blind rewriting.
*)

Ltac2 rec get_head (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => get_head f
  | Constr.Unsafe.Cast c _ _ => get_head c
  | _ => t
  end.

Example test_get_head : forall (A B : Type) (f : A -> A -> B) (x y : A), 
  True.
Proof.
  intros A B f x y.
  
  (* Define the check logic locally *)
  let check (t : constr) (expected : constr) (msg : string) :=
    let res := get_head t in
    if Constr.equal res expected then () 
    else Control.throw (Tactic_failure (Some (Message.of_string msg)))
  in
  let f := 'f in
  let x := 'x in
  
  (* Test 1: Simple application (f x) -> f *)
  check '(f x) f "Failed to get head of (f x)";
  (* Test 2: Nested application (f x y) -> f *)
  check '(f x y) f "Failed to get head of (f x y)";
  (* Test 3: Casted term ((f x) : B) -> f *)
  check '((f x y) : B) f "Failed to get head of cast";
  (* Test 4: Raw variable x -> x *)
  check x x "Failed to get head of var".

  exact I.
Qed.

Ltac2 rec get_codomain (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ body => get_codomain body
  | _ => t
  end.

Example test_get_codomain : forall (A : Type), 
  (A -> bool) -> 
  (forall (x:A), sumbool True True) -> 
  (forall (x:A), {x = x} + {x <> x}) -> 
  True.
Proof.
  intros A f_bool f_sum f_sum2.

  let check_is_bool (t : constr) :=
    let res := get_codomain t in
    match! res with
    | bool => ()
    | _ => Control.throw (Tactic_failure (Some (Message.of_string "Expected bool")))
    end
  in
  let check_is_sumbool (t : constr) :=
    let res := get_codomain t in
    match! res with
    | sumbool _ _ => ()
    | _ => Control.throw (Tactic_failure (Some (Message.of_string "Expected sumbool")))
    end
  in
  (* Test 1: Simple Type (bool) *)
  check_is_bool 'bool;

  (* Test 2: Arrow Type (A -> bool) *)
  check_is_bool (Constr.type 'f_bool);

  (* Test 3: Dependent Product (forall x, sumbool ...) *)
  check_is_sumbool (Constr.type 'f_sum);

  (* Test 4: Sumbool with forall (forall x, sumbool ...) *)
  check_is_sumbool (Constr.type 'f_sum2).

  exact I.
Qed.

Ltac2 dest_match (t : constr) : unit :=
  let no_eqn := 
    match! Constr.type t with
    | sumbool _ _ => true
    | bool => Constr.is_var t
    | _ => false
    end
  in
  if no_eqn then destruct $t
  else 
    let heq := fresh_hyp "Heq" in
    destruct $t eqn:$heq.

Example test_dest_match_comprehensive : 
  forall (n : nat) (b : bool) (s : {1=1} + {1=2}),
  Nat.eqb n 0 = true -> (* Boolean application *)
  (if Compare_dec.zerop n then 1 else 0) = 0 -> (* Sumbool application *)
  True.
Proof.
  intros n b s Hbool Hsum.

  (* Define assertion logic locally to keep environment clean *)
  let assert_heq (should_exist : bool) := 
    let hyps := Control.hyps () in
    let found := List.exist (fun (id, _, _) => Ident.equal id @Heq) hyps in
    if Bool.equal found should_exist then ()
    else 
      let msg := if should_exist then "Expected Heq, found none" else "Found Heq, expected none" in
      Control.throw (Tactic_failure (Some (Message.of_string msg)))
  in

  (* 1. Standard Inductive (nat) -> Expect Heq *)
  dest_match 'n > [ 
    assert_heq true
    | assert_heq true; apply I 
  ]; 
  clear n Heq;
  (* 2. Boolean Variable -> Expect NO Heq *)
  dest_match 'b > [
    assert_heq false
    | assert_heq false; apply I 
  ];
  clear b;
  (* 3. Sumbool Variable -> Expect NO Heq *)
  dest_match 's > [
    assert_heq false
  | assert_heq false; apply I
  ];
  clear s;
  (* 4. Boolean Application (Nat.eqb) -> Expect Heq *)
  (* This proves the "is_complex" check works *)
  dest_match '(Nat.eqb 0 0) > [
    assert_heq true
  | assert_heq true; apply I 
  ];
  clear Hbool Heq;
  (* 5. Sumbool Application (Compare_dec.zerop) -> Expect NO Heq *)
  (* This proves the "codomain" check works *)
  dest_match '(Compare_dec.zerop 0) > [
    assert_heq false
  | assert_heq false; apply I 
  ].
  
  apply I.
Qed.

Example dest_match_works : forall (x : nat) (l : list nat) (b : bool) 
  (p : { 1 = 1 } + { 1 = 2 }),
  (match x with
    | 0 => true
    | S _ => true
    end = true
  ) ->
  (match l with
    | [] => 0
    | _ :: _ => 0
  end = 0) ->
  ((if b then 0 else 0) = 0) ->
  ((if p then 0 else 0) = 0) ->
  True.
Proof.
  intros x l b p Hx Hl Hb Hp.
  let assert_hyp should_exist h := 
    let hyps := Control.hyps () in
    match List.find_opt (fun (i, _, _) => Ident.equal i h) hyps with
    | Some _ => if should_exist then () else fail
    | None => if should_exist then fail else ()
    end
  in
  dest_match 'x > [ 
    assert_hyp true ident:(Heq) 
    (* solve second just to be simple*)
    | assert_hyp true ident:(Heq); apply I 
  ]; clear Heq Hx x;
  dest_match 'l > [ 
    assert_hyp true ident:(Heq) 
    (* solve second just to be simple*)
    | assert_hyp true ident:(Heq); apply I 
  ]; clear Heq Hl l;
  (* NOTE for the next two, they don't create Heq
    since they are bool~ish and its just garbage in the environment
  *)
  dest_match 'b > [ 
    assert_hyp false ident:(Heq) 
    (* solve second just to be simple*)
    | assert_hyp false ident:(Heq); apply I 
  ]; clear Hb b;
  dest_match 'p > [ 
    assert_hyp false ident:(Heq) 
    (* solve second just to be simple*)
    | assert_hyp false ident:(Heq); apply I 
  ]; clear Hp p.
  apply I.
Qed.

(* OPTIMIZATION: Filter out "Boring" hypotheses. 
   We don't want to grind 'n : nat', 'A : Type', or 'H : A -> B'.
   We only want to grind "Data" (And, Or, Exists, Eq) or "Contradictions" (False). *)
Ltac2 is_inert (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var _ => true  (* n : nat *)
  | Constr.Unsafe.Sort _ => true (* A : Type *)
  | Constr.Unsafe.Prod _ _ => true (* H : A -> B (Keep these for the solver, don't grind) *)
  | Constr.Unsafe.Ind _ _ => 
       (* Check for False! False is an Inductive, but it is NOT inert. *)
       if Constr.equal c '(False) then false else true 
  | _ => false
  end.

(* Collect only "Interesting" hypotheses to seed the queue *)
Ltac2 active_hyps () : ident list :=
  List.fold_left 
    (fun acc (i, _, ty) => 
      if Bool.neg (is_inert ty) then i :: acc else acc) 
    [] 
    (Control.hyps ()).

(* The Worklist Grinder. 
   It takes a list of hypothesis IDs. It pops one, processes it, 
   and pushes NEW hypotheses onto the stack.
   It runs until the stack is empty (Fixed Point).
*)
Ltac2 grinder (queue : ident list) :=
  let restart g  := 
    (* SUBST RUINS THE QUEUE. 
      Refill with ALL current hyps to be safe. *)
    g (active_hyps ())
  in
  let rec aux q := 
    try (simple congruence 1);
    match q with
    | [] => () (* Done *)
    | hid :: rest =>
      match safe_hyp hid with
      | None => aux rest (* It's gone, skip *)
      | Some (name, _val, type) =>
        let hv := Control.hyp name in
        (* Check for trivial contradictions first *)
        if is_reflexive type then (
          (* we have to do "try" here because it may be
          used in other hypotheses *)
          try (clear $name); 
          aux rest
        ) 
        else if is_discr_equality type then (exfalso; congruence) 
        (* 3. Injectable Equality: S n = S m *)
        else if is_injectable_equality type then (
          (* Inject, get new IDs (n=m), and ADD them to the queue *)
          try (
            inject_and_subst name;
            restart aux
          )
        )
        else
          (* Inspect type structure *)
          lazy_match! type with
          | False => exfalso; assumption
          | _ /\ _ =>
              (* Split and add children to queue *)
              let h1 := fresh_hyp "Hand_l" in
              let h2 := fresh_hyp "Hand_r" in
              destruct $hv as [$h1 $h2];
              aux (h1 :: h2 :: rest)
          
          | _ \/ _ =>
              (* Branching! We must recurse in BOTH branches. *)
              let h1 := fresh_hyp "Hor_l" in
              let h2 := fresh_hyp "Hor_r" in
              (* logic: destruct, then in each branch, continue grinding with the specific new hyp *)
              destruct $hv as [$h1 | $h2] > 
              [ aux (h1 :: rest) | aux (h2 :: rest) ]
          
          | { _ } + { _ } =>
              (* Branching! We must recurse in BOTH branches. *)
              let h1 := fresh_hyp "Hsumb_l" in
              let h2 := fresh_hyp "Hsumb_r" in
              (* logic: destruct, then in each branch, continue grinding with the specific new hyp *)
              destruct $hv as [$h1 | $h2] > 
              [ aux (h1 :: rest) | aux (h2 :: rest) ]
          
          | exists _, _ =>
              let h_body := fresh_hyp "Hex" in
              destruct $hv as [? $h_body];
              aux (h_body :: rest)

          (* Optional: Match Context Scanning 
              Only doing this on hypotheses can be aggressive. 
              Enable if you really need it. *)
          | context [ match ?v with _ => _ end ] =>
                (* Warning: This can loop if dest_match doesn't eliminate the match. *)
              dest_match v; Control.enter (fun () => restart aux)
              
          | ?x = ?y =>
              (* Subst logic *)
              let substed := 
                (* we wrap in a "plus" because subst can fail if recursive equality! *)
                Control.plus (fun () => 
                  match Constr.Unsafe.kind x with
                  | Constr.Unsafe.Var xid => Std.subst [xid]; true
                  | _ => 
                    match Constr.Unsafe.kind y with
                    | Constr.Unsafe.Var yid => Std.subst [yid]; true
                    | _ => false
                    end
                  end
                )
                (fun _ => false)
              in
              if substed 
              then Control.once (fun () => restart aux) 
              else Control.once (fun () => try (rewrite $hv in *); aux rest)
                
          | _ => aux rest
          end
      end
    end
  in
  aux queue.

(* Entry point for cleaning context *)
Ltac2 saturate_context () :=
  grinder (active_hyps ()).

Ltac2 sprintf fmt := 
  Message.Format.kfprintf (fun x => Message.to_string x) fmt.

Ltac2 Notation "sprintf" fmt(format) := sprintf fmt.

Ltac2 dprint (debug : bool) :=
  let tab_char := Char.of_int 9 in
  fun (tabs : int) (s : string) =>
    if debug 
    then (printf "%s%s" (String.make tabs tab_char) s) 
    else ().

Ltac2 rescue debug leaf_solver inter_solver d rec_F :=
  dprint debug d "Crush: Rescue";

  let progressed := Control.plus 
    (fun () => 
        dprint debug d "Crush: Fall-through";
        progress (fun () => 
          try (leaf_solver ());
          try (inter_solver ());
          cbn in *
        ); 
        true)
    (fun _ => false)
  in
  if progressed then (
      (* CBN worked, so we recurse *)
      rec_F (Int.add d 1)
  ) else (
      (* Both failed. This is a hard failure. *)
      dprint debug d "Crush: Rescue Failure - No progress with cbn!"
  ).

(* --- THE UNIFIED LOOP --- *)
Ltac2 crush1 
    (debug : bool)
    (* (inter_solver : unit -> unit)  *)
    (rec_F : int -> unit)
    (d : int)
    (rescue : int -> (int -> unit) -> unit) :=
  dprint debug d "Crush: Saturating Context";
  saturate_context ();
  Control.enter (fun () => 
    (* dprint debug d "Crush: Trying Inter-solver";
    try (inter_solver ()); *)
    Control.enter (fun () =>
      dprint debug d "Crush: Analyzing Goal";
      lazy_match! goal with
      | [ |- ~ _ ] =>
          dprint debug d "Crush: Negation";
          let hc := fresh_hyp "HC" in
          intro $hc; rec_F d

      | [ |- _ <-> _ ] => 
          dprint debug d "Crush: Iff";
          split > [ 
            Control.once (fun () =>
              dprint debug d "Crush: Iff Left"; rec_F (Int.add d 1))
            | 
            Control.once (fun () =>
              (dprint debug d "Crush: Iff Right"; rec_F (Int.add d 1))
            )
          ]

      | [ |- _ /\ _ ] => 
          dprint debug d "Crush: And";
          split > [ 
            Control.once (fun () =>
              dprint debug d "Crush: And Left"; rec_F (Int.add d 1))
            | 
            Control.once (fun () =>
              (dprint debug d "Crush: And Right"; rec_F (Int.add d 1))
            )
          ]
          
      | [ |- forall _, _ ] => 
        dprint debug d "Crush: Forall";
        let v := get_forall_var_name (Control.goal ()) in
        let x := fresh_hyp (Ident.to_string v) in
        intros $x; rec_F d

      | [ |- context [ match ?t with _ => _ end ] ] =>
          dprint debug d "Crush: Match in Goal";
          let goal_num := Ref.ref 1 in
          dest_match t; 
          Control.enter (fun () => 
            dprint debug d (sprintf "Crush: Match in Goal Branch %i" (Ref.get goal_num));
            Ref.incr goal_num;
            rec_F (Int.add d 1)
          )

      (* 
      I don't like this case a lot: it should typically be 
      unnecessary, but sometimes "inter_solver" will create
      a match in a hypothesis that needs to be broken down before we can make progress.
      *)
      | [ _h : context [ match ?_t with _ => _ end ] |- _ ] =>
          dprint debug d "Crush: Match in Hypothesis";
          (* don't increase depth here, 
          since we aren't making "real" progress on the goal, just rearranging context 
          *)
          try (
            progress (fun () =>
              cbn in *;
              saturate_context ()
            );
            Control.enter (fun () => rec_F d)
          )


      (* NOTE: These are intentionally after the 
        "match destruction" step, because it may be the case
        that the depending on the outcome of the match, the branch/
        eexists picked will be different.

        Essentially: 
        "it is best to PICK a branch/variable as late as possible"
      *)
      | [ |- { _ } + { _ } ] => 
          dprint debug d "Crush: Sumbool";
          try (
            solve [ 
              dprint debug d "Crush: Sumbool Left";
              left; rec_F (Int.add d 1)
            ]
          );
          try (
            solve [ 
              dprint debug d "Crush: Sumbool Right";
              right; rec_F (Int.add d 1) 
            ]
          );
          dprint debug d "Crush: Sumbool Failed!";
          rescue d rec_F
      
      | [ |- _ \/ _ ] => 
          dprint debug d "Crush: Or";
          try (
            solve [ 
              dprint debug d "Crush: Or Left";
              left; rec_F (Int.add d 1) 
            ]
          );
          try (
            solve [ 
              dprint debug d "Crush: Or Right";
              right; rec_F (Int.add d 1) 
            ]
          );
          dprint debug d "Crush: Or Failed!";
          rescue d rec_F
          
      | [ |- exists _, _ ] => 
        dprint debug d "Crush: Exists";
        (* only lock in existentials if solving *)
        try (eexists; solve [ rec_F (Int.add d 1) ]);
        dprint debug d "Crush: Exists Failed!";
        rescue d rec_F

      (* --------------------------------------------------------- *)
      (* TRY REDUCTION *)
      (* --------------------------------------------------------- *)
      | [ |- _ ] => 
        (* only option: hope for rescue!!! *)
        dprint debug d "Crush: Fall-through Case";
        rescue d rec_F
      end
    )
  ).

Ltac2 crush_once0 debug tacs :=
  let res_tac () := eauto; reflexivity in
  let inter_tac := tac_list_thunk tacs in
  crush1 
    debug
    (fun _ => ()) 
    0 
    (rescue debug res_tac inter_tac).

Ltac2 Notation "crush_once" 
  tacs(opt(seq("with", list0(thunk(tactic(0)), ",")))) :=
  crush_once0 false tacs.

Ltac2 Notation "dcrush_once" 
  tacs(opt(seq("with", list0(thunk(tactic(0)), ",")))) :=
  crush_once0 true tacs.

Ltac2 crush_loop 
    (debug : bool)
    (inter_solver : unit -> unit) 
    (leaf_solver : unit -> unit) :=
  let rec aux d := 
    crush1 debug aux d 
      (rescue debug leaf_solver inter_solver)
  in
  aux 0.

Ltac2 rec find_relevant_entry (comp : constr) (vl : constr) :=
  match! vl with
  | nil => Control.zero (Tactic_failure None)
  | ((?c, (?c_stat, ?c_typ, ?c_next_cor)) :: ?rest) =>
    (* check if the head matches *)
    if Constr.equal comp c
    then (c_stat, c_typ, c_next_cor)
    else find_relevant_entry comp rest
  end.

Ltac2 Notation "find_relevant_entry" comp(constr) map(constr) := 
  find_relevant_entry comp map.

Ltac2 ff0 debug inter_tac :=
  let res_tac () := eauto; reflexivity in
  Control.enter (fun () =>
    try (res_tac ());
    try (inter_tac ());
    Control.enter (fun () => crush_loop debug inter_tac res_tac)
  ).

Ltac2 Notation "ff" 
  tacs(opt(seq("with", list0(thunk(tactic(0)), ",")))) :=
  ff0 false (tac_list_thunk tacs).

Ltac2 Notation "dff" 
  tacs(opt(seq("with", list0(thunk(tactic(0)), ",")))) :=
  ff0 true (tac_list_thunk tacs).

Ltac2 Notation "fwd" :=
  Control.enter (fun () =>
    match! goal with
    | [ h : ?h1 -> ?_h2 |- _ ] =>
      let ha := fresh_hyp "Ha" in
      assert ($h1) as $ha by ff; 
      let hv := Control.hyp h in
      let hav := Control.hyp ha in
      pp ($hv $hav); clear $h $ha
    end
  ).

(* Simplification hammer.  Used at beginning of many proofs in this 
   development.  Conservative simplification, break matches, 
   invert on resulting goals *)
Ltac2 rec ff_old tac :=
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
      break_or_hyp; ff_old tac; 
      ltac1:(num |- let num2 := numgoals in
      guard num2 <= num) (Ltac1.of_int num))
  ).

Ltac2 Notation "lia" := ltac1:(lia).
Ltac2 Notation lia := lia.

Ltac2 Notation l := try lia.
Ltac2 u0 () := ltac1:(repeat autounfold in *).
Ltac2 Notation u := u0 ().

(* [ux dbs] is a tactic that unfolds the given databases, and always
   includes the core database. *)
Ltac2 autounfold_dbs dbs :=
  (List.fold_left
    (fun _acc db => ltac1:(db |- repeat (autounfold with db in *)) (Ltac1.of_ident db)) 
    (ltac1:(repeat autounfold in *))
    dbs);
  ltac1:(repeat autounfold in *).
Ltac2 ux0 dbs := 
  (* Always utilize core, but optionally can include extra *)
  fun () =>
  autounfold_dbs (ident:(core) :: dbs).
Ltac2 Notation "ux" dbs(list0(ident, ",")) := ux0 dbs.
Ltac2 Notation ux := ux.

Ltac2 a0 () := repeat find_apply_hyp_hyp.
Ltac2 Notation a := a0 ().
Ltac2 Notation r := rw_all.
Ltac2 v0 () := vm_compute.
Ltac2 Notation v := v0 ().
Ltac2 d0 () := printf "DebugPrint".
Ltac2 Notation d := d0 ().

(* [interp_tac_str] interprets a string as a sequence of tactics. *)

Ltac2 ff_old_core tac_list :=
  let tac := tac_list_thunk tac_list in
  repeat (
    ff_old tac;
    tac ();
    ff_old tac
  ).

Ltac2 Notation "ff_old" 
  tacs(opt(list0(tactic(0), ","))) 
  :=
  (* Default timeout of 30 seconds *)
  Control.timeout 30 (fun () => ff_old_core tacs).

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
Ltac2 Notation "target_break_match"
  h(ident) :=
  target_break_match h.

Ltac2 Notation "setoid_rw_all" h(constr) :=
  repeat (
    match! goal with
    | [ h' : context [ ?_x ] |- _ ] => 
      setoid_rewrite $h in $h'
    | [ |- context [ ?_x ] ] => 
      setoid_rewrite $h
    end;
    subst_max;
    eauto;
    try (simple congruence 1)
  ).