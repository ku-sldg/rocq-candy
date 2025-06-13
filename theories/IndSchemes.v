From RocqCandy Require Import Tactics.
From Stdlib Require Export Nat Lia.

(**
  This file contains various "induction schemes" that might be useful.

  In particular, we don't just mean "schemes" that could be used with "induction <x> using <y>", but more abstractly any scheme that can be used to prove some Prop "P : A -> Prop" forall "x : A"
*)

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
    assert (n = Nat.modulo n k) by (pp (PeanoNat.Nat.mod_unique n k 0 n); ff l).
    rewrite H.
    eapply fMod.
  - (* Case: n >= k *)
    (* We can apply the division and modulo functions *)
    assert (fModDivNext : forall n0 : nat, P (Nat.div n0 k) -> P n0) by ff.
    assert (Nat.div n k < k \/ Nat.div n k >= k) as [Hdiv_lt | Hdiv_ge] by lia.
    * (* Case: (n // k) < k *)
      (* Just another base case *)
      assert (Nat.div n k = Nat.modulo (Nat.div n k) k) by
        (pp (PeanoNat.Nat.mod_unique (n / k) k 0 (n / k)); ff l).
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

Theorem fold_right_ind : forall {A B : Type} 
  (P : A -> Prop)
  (f : B -> A -> A) (ls : list B) (init : A),
  (forall x, P x -> forall y, P (f y x)) ->
  (P init \/ exists x', In x' ls /\ (forall y, P (f x' y))) ->
  P (fold_right f init ls).
Proof.
  intuition.
  - induction ls; eauto.
  - break_exists; intuition;
    induction ls; simpl in *; intuition; eauto.
    subst; eauto.
Defined.
