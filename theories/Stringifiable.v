From Stdlib Require Export String.
From Stdlib Require Import Ascii.
Local Open Scope string_scope.
From RocqCandy Require Import Tactics ResultMonad SPropTools.
Import ResultNotation.

Class Stringifiable (A : Type) := {
  to_string                   : A -> string ;
  from_string                 : string -> (Result A string) ;
  canonical_stringification   : forall a, 
    from_string (to_string a) = res a 
}.

Global Instance Stringifiable_string : Stringifiable string := {
  to_string := fun s => s;
  from_string := fun s => res s;
  canonical_stringification := fun s => eq_refl;
}.

Global Instance Stringifiable_bool : Stringifiable bool := {
  to_string := fun b => if b then "true" else "false";
  from_string := fun s => 
                  if String.eqb s "true" 
                  then res true
                  else if String.eqb s "false" 
                  then res false
                  else err "Not a boolean";
  canonical_stringification := fun b =>
                                  match b with
                                  | true => eq_refl
                                  | false => eq_refl
                                  end;
}.

Module Nat_Stringification.

  Inductive lt_sprop : nat -> nat -> SProp :=
  | lt_sprop_O : forall n, lt_sprop O (S n)
  | lt_sprop_s : forall n m, 
      lt_sprop n m -> 
      lt_sprop (S n) (S m).

  Fixpoint nat_lts (n m : nat) : SProp :=
    match n, m with
    | O, O => SFalse
    | O, S _ => STrue
    | S _, O => SFalse
    | S n', S m' => nat_lts n' m'
    end.

  Lemma nat_lts_lt : forall n m,
    Box (nat_lts n m) <-> lt n m.
  Proof.
    induction n; ff l; box_simpl.
    - find_eapply_lem_hyp IHn; ff l.
    - erewrite IHn; lia.
  Qed.

  Theorem lt_sprop_impl_nat_lts : forall {n m},
    lt_sprop n m -> nat_lts n m.
  Proof.
    induction n; ff; try (inv H); ff.
  Qed.

  Theorem nat_lts_impl_lt_sprop : forall {n m},
    nat_lts n m -> lt_sprop n m.
  Proof.
    induction n; ff; try (inv H); ff;
    econstructor; ff.
  Qed.

  Lemma nat_lts_dec : forall n m,
    { Box (nat_lts n m) } + { ~ Box (nat_lts n m) }.
  Proof.
    induction n; ff; try find_contra;
    right; intro HC; inv HC; inv unbox.
  Defined.

  Lemma nat_modulo_eq : forall n k,
    k <> 1 -> 
    n < k ->
    n = Nat.modulo n k.
  Proof.
    intros.
    pp (PeanoNat.Nat.mod_unique n k 0 n).
    lia.
  Qed.
  
  Definition nat_div_mod_ind (k : nat) 
    `{HK : k <> 1}
    (P : nat -> Prop)
    (* So long as we can handle every "n" s.t. "n % k == l" *)
    (* And any "n" s.t. "n / k" *)
    (fMod : forall n, P (Nat.modulo n k))
    (fModDiv : forall n,
      P (Nat.modulo n k) ->
      P (Nat.div n k) ->
      P n) :
   forall n, P n.
  Proof.
    ref (Fix PeanoNat.Nat.lt_wf_0 _ (fun n F => _)).
    assert (n < k \/ n >= k) as [Hlt | Hge] by lia.
    - (* Case: n < k *)
      (* We can just apply a Modulo *)
      assert (n = Nat.modulo n k) by (eapply nat_modulo_eq; ff).
      rewrite H.
      eapply fMod.
    - (* Case: n >= k *)
      (* We can apply the division and modulo functions *)
      assert (fModDivNext : forall n0 : nat, P (Nat.div n0 k) -> P n0) by ff.
      assert (Nat.div n k < k \/ Nat.div n k >= k) as [Hdiv_lt | Hdiv_ge] by lia.
      * (* Case: (n // k) < k *)
        (* Just another base case *)
        assert (Nat.div n k = Nat.modulo (Nat.div n k) k) by (eapply nat_modulo_eq; ff).
        eapply (fModDiv _ (fMod _)).
        rewrite H.
        eapply fMod.
      * (* Case: (n // k) >= k *)
        (* This is the truly recursive case *)
        assert (k = 0 \/ k = 1 \/ k > 1) as [Hk_eq_0 | [ Hk_eq_1 | Hk_gt_1]] by lia.
        + (* Case: k = 0 *)
          subst.
          simpl in *.
          eapply fMod.
        + (* Case: k = 1*)
          (* This is outlawed! *)
          lia.
        + (* Case: k > 1 *)
          subst.
          ref (fModDivNext _ (F _ _)).
          eapply PeanoNat.Nat.div_lt; lia.
  Qed.

  Local Open Scope char_scope.
  Definition nat_lt_10_to_ascii (n : nat) (HN : lt_sprop n 10) : ascii.
  ref (
    match n as n' return n = n' -> ascii with
    | O => fun _ => "0"
    | S O => fun _ => "1"
    | S (S O) => fun _ => "2"
    | S (S (S O)) => fun _ => "3"
    | S (S (S (S O))) => fun _ => "4"
    | S (S (S (S (S O)))) => fun _ => "5"
    | S (S (S (S (S (S O))))) => fun _ => "6"
    | S (S (S (S (S (S (S O)))))) => fun _ => "7"
    | S (S (S (S (S (S (S (S O))))))) => fun _ => "8"
    | S (S (S (S (S (S (S (S (S O)))))))) => fun _ => "9"
    | _ => fun HNN => False_rect _ _
    end eq_refl).
    destruct (nat_lts_dec n 10); subst; simpl in *.
    - erewrite nat_lts_lt in *; try lia.
    - eapply lt_sprop_impl_nat_lts in HN; simpl in *; eauto.
  Defined.

  Definition nat_lt_10_from_ascii (c : ascii) : Result { n | Box (lt_sprop n 10) } string :=
    let n_val := Ascii.nat_of_ascii c in
    let n_c := n_val - 48 in
    match nat_lts_dec n_c 10 with
    | left (box H) => res (exist _ n_c (box (nat_lts_impl_lt_sprop H)))
    | right H => err "Character is not a digit"%string
    end.
  Close Scope char_scope.

  Lemma nat_lt_10_ascii_invol : forall n (HN : lt_sprop n 10),
    nat_lt_10_from_ascii (nat_lt_10_to_ascii n HN) = res (exist _ n (box HN)).
  Proof.
    induction n; ff l; try (ltac1:(exfalso; eauto; fail)); box_simpl.
    - eapply lt_sprop_impl_nat_lts in HN as HN'; simpl in *; box_simpl.
    - eapply lt_sprop_impl_nat_lts in HN as HN'; simpl in *; box_simpl.
    - eapply lt_sprop_impl_nat_lts in HN as HN'; simpl in *; box_simpl.
  Qed.
  Opaque nat_lt_10_to_ascii nat_lt_10_from_ascii.

  Lemma n_mod_10_lt_spec : forall n,
    ~ Box (nat_lts n 10) ->
    Nat.modulo n 10 < n.
  Proof.
    intros.
    erewrite nat_lts_lt in *.
    ff l.
  Qed.

  Lemma n_mod_10_lt_10 : forall n,
    Nat.modulo n 10 < 10.
  Proof.
    ff l.
  Qed.

  Lemma n_mod_sprop : forall n,
    lt_sprop (Nat.modulo n 10) 10.
  Proof.
    intros.
    eapply nat_lts_impl_lt_sprop.
    pp (n_mod_10_lt_10 n).
    erewrite <- nat_lts_lt in *.
    ff.
  Qed.

  Lemma n_div_10_lt_n : forall n,
    ~ (Box (nat_lts n 10)) ->
    Nat.div n 10 < n.
  Proof.
    intros; eapply PeanoNat.Nat.div_lt; ff l.
    erewrite nat_lts_lt in *.
    lia.
  Qed.

  Definition nat_to_string : nat -> string :=
    Fix PeanoNat.Nat.lt_wf_0 _ 
    (fun n F => 
      match nat_lts_dec n 10 with
      | left (box H) => String (nat_lt_10_to_ascii n (nat_lts_impl_lt_sprop H)) EmptyString
      | right (H) => (String.append (F (Nat.div n 10) (n_div_10_lt_n n H)) (F  (Nat.modulo n 10) (n_mod_10_lt_spec _ H)))
      end).

  Theorem nat_to_string_eq : forall n,
    nat_to_string n = match nat_lts_dec n 10 with
      | left (box H) => String (nat_lt_10_to_ascii n (nat_lts_impl_lt_sprop H)) EmptyString
      | right (H) => (String.append (nat_to_string (Nat.div n 10)) (nat_to_string (Nat.modulo n 10)))
      end.
  Proof.
    intros.
    unfold nat_to_string at 1.
    erewrite Fix_eq; ff.
  Qed.

  (* TODO: Make this tail recursive! *)
  Fixpoint string_to_nat (s : string) : Result nat string :=
    match s with
    | EmptyString => err "Empty string cannot be converted to a number"
    | String c rest =>
      '(exist _ n _) <- nat_lt_10_from_ascii c ;;
      match rest with
      | EmptyString => res n
      | _ => 
        n_rec <- string_to_nat rest ;;
        res (n * (Nat.pow 10 (String.length rest)) + n_rec)
      end
    end.
  Local Opaque Nat.modulo Nat.div.

  Lemma string_length_app : forall s1 s2,
    String.length (String.append s1 s2) = String.length s1 + String.length s2.
  Proof.
    induction s1; ff.
  Qed.
  
  Theorem string_to_nat_app : forall s1 n1,
    string_to_nat s1 = res n1 ->
    forall s2 n2,
    string_to_nat s2 = res n2 ->
    string_to_nat (String.append s1 s2) = res (n1 * (Nat.pow 10 (String.length s2)) + n2).
  Proof.
    induction s1; intros.
    - ff.
    - simpl in *; unfold bind in *.
      break_match; subst; simpl in *; try congruence.
      destruct s1.
      * simpl.
        erewrite H0; ff.
      * destruct (string_to_nat (String a0 s1)) eqn:E; try congruence.
        erewrite (IHs1 _ eq_refl _ _ H0).
        break_match.
        ** ff.
        ** clear IHs1 H0; clean.
          assert (x * Nat.pow 10 (length (String a0 s1)) + n = n1) by ff.
          clear H; erewrite <- H0; clear H0.
          assert (length (String a1 s) = length (String a0 s1 ++ s2)) by ff.
          erewrite H in *.
          erewrite string_length_app in *.
          simpl.
          erewrite PeanoNat.Nat.pow_add_r.
          f_equal.
          lia.
  Qed.

  Theorem nat_to_string_from_string : forall n,
    string_to_nat (nat_to_string n) = res n.
  Proof.
    assert (10 <> 1) as HK by lia.
    induction n using (@nat_div_mod_ind 10 HK); clear HK.
    - set (n' := Nat.modulo n 10).
      assert (n' = 0 \/ n' = 1 \/ n' = 2 \/ n' = 3 \/ n' = 4 \/ n' = 5 \/ n' = 6 \/ n' = 7 \/ n' = 8 \/ n' = 9). {
        assert (n' < 10) as Hlt by (eapply n_mod_10_lt_10; ff).
        lia.
      }
      clearbody n'.
      repeat break_or_hyp; rewrite nat_to_string_eq; ff u.
    - rewrite nat_to_string_eq.
      break_match; break_match; simpl; try congruence; ff u;
      try (erewrite nat_lt_10_ascii_invol in *); ff.
      erewrite (string_to_nat_app _ _ IHn0 _ _ IHn).
      assert (length (nat_to_string (Nat.modulo n 10)) = 1). {
        set (n' := Nat.modulo n 10).
        assert (n' = 0 \/ n' = 1 \/ n' = 2 \/ n' = 3 \/ n' = 4 \/ n' = 5 \/ n' = 6 \/ n' = 7 \/ n' = 8 \/ n' = 9) by (assert (n' < 10) as Hlt by (eapply n_mod_10_lt_10; ff); lia).
        repeat break_or_hyp; ff; rewrite nat_to_string_eq; ff u.
      }
      rewrite H.
      simpl.
      f_equal.
      pp (PeanoNat.Nat.Div0.div_mod n 10).
      lia.
  Qed.
  Global Opaque nat_to_string string_to_nat.
End Nat_Stringification.

Global Instance Stringifiable_nat : Stringifiable nat := {
  to_string := Nat_Stringification.nat_to_string ;
  from_string := Nat_Stringification.string_to_nat ;
  canonical_stringification := Nat_Stringification.nat_to_string_from_string
}.