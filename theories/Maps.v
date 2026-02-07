(*
Association List Based Map Library

This library provides a map implementation using association lists,
with theorems about map operations and their properties.
*)

From Stdlib Require Import List Bool Decidable Streams StrictProp.
From RocqCandy Require Import DecEq Tactics.
Import ListNotations.

Global Create HintDb maps.
Section Maps.

  Context {K : Type} `{DK : DecEq K}.

  (* Map is represented as an association list of key-value pairs *)
  Definition Map K V := list (K * V).

  (* Empty map *)
  Definition empty {V} : Map K V := [].

  (* Lookup operation - returns Some value if key exists, None otherwise *)
  Fixpoint lookup {V} (k : K) (m : Map K V) : option V :=
    match m with
    | [] => None
    | (k', v) :: rest => 
      if dec_eq k k' 
      then Some v
      else lookup k rest
    end.

  (* Insert/Update operation - adds or updates a key-value pair *)
  Fixpoint insert {V} (k : K) (v : V) (m : Map K V) : Map K V :=
    match m with
    | [] => [(k, v)]
    | (k', v') :: rest =>
      if dec_eq k k' 
      then (k, v) :: rest
      else (k', v') :: insert k v rest
    end.

  (* Remove operation - removes a key from the map *)
  Fixpoint remove {V} (k : K) (m : Map K V) : Map K V :=
    match m with
    | [] => []
    | (k', v') :: rest =>
      if dec_eq k k' 
      (* sucks, but we have to recurse to get nice theorems *)
      then remove k rest 
      else (k', v') :: remove k rest
    end.

  Fixpoint mapify {V} (l : Map K V) : Map K V :=
    match l with
    | [] => empty
    | (k, v) :: rest => insert k v (mapify rest)
    end.

  Definition map_join {V} (m1 m2 : Map K V) : Map K V :=
    mapify (m1 ++ m2).

  (* Size of the map (number of key-value pairs) *)
  Definition map_size {V} (m : Map K V) : nat := length m.
  (* Check if map is empty *)
  Definition is_empty {V} (m : Map K V) : bool :=
    match m with
    | [] => true
    | _ => false
    end.

  (* Map function over values *)
  Fixpoint map_values {V V'} (f : V -> V') (m : Map K V) : Map K V' :=
    match m with
    | [] => []
    | (k, v) :: rest => (k, f v) :: map_values f rest
    end.

  (* Filter map by predicate on key-value pairs *)
  Fixpoint map_filter {V} (p : K -> V -> bool) (m : Map K V) : Map K V :=
    match m with
    | [] => []
    | (k, v) :: rest =>
      if p k v
      then (k, v) :: map_filter p rest
      else map_filter p rest
    end.

  Fixpoint map_Map {V V'} (f : K -> V -> V') (m : Map K V) : Map K V' :=
    match m with
    | [] => []
    | (k, v) :: rest => (k, f k v) :: map_Map f rest
    end.

  Lemma lookup_map_Map {V V'} (f : K -> V -> V') (m : Map K V) (k : K) :
    lookup k (map_Map f m) = 
      match lookup k m with
      | Some v => Some (f k v)
      | None => None
      end.
  Proof.
    induction m; ff.
  Qed.

  Inductive valid_map {V} : Map K V -> Prop :=
  | valid_map_empty : valid_map (@empty V)
  | valid_map_insert : forall (m : Map K V) (k : K) (v : V),
      valid_map m ->
      lookup k m = None ->
      valid_map (insert k v m).

  (* Basic lookup theorems *)
  Theorem lookup_empty : forall {V : Type} (k : K),
    @lookup V k empty = None.
  Proof.
    ff.
  Qed.
  Hint Resolve lookup_empty : maps.

  Lemma insert_not_empty : forall {V} k m (v : V),
    insert k v m = empty ->
    False.
  Proof.
    induction m; ff; unfold empty in *; ff.
  Qed.
  Hint Resolve insert_not_empty : maps.

  Theorem lookup_impl_in : forall {V} (k : K) (m : Map K V) (v : V),
    lookup k m = Some v -> 
    In (k, v) m.
  Proof.
    induction m; ff.
  Qed.
  Hint Resolve lookup_impl_in : maps.

  Theorem lookup_insert_neq : forall V (k k' : K) (v : V) (m : Map K V),
    k <> k' -> 
    lookup k (insert k' v m) = lookup k m.
  Proof.
    induction m; ff.
  Qed.
  Hint Rewrite -> lookup_insert_neq : maps.

  Theorem lookup_insert_eq : forall V (k : K) (v : V) (m : Map K V),
    lookup k (insert k v m) = Some v.
  Proof.
    induction m; ff.
  Qed.
  Hint Rewrite -> lookup_insert_eq : maps.

  Theorem lookup_remove_eq : forall V (m : Map K V) k,
    lookup k (remove k m) = None.
  Proof.
    induction m; ff.
  Qed.
  Hint Resolve lookup_remove_eq : maps.

  Theorem lookup_remove_neq : forall V (k k' : K) (m : Map K V),
    k <> k' -> 
    lookup k (remove k' m) = lookup k m.
  Proof.
    induction m; ff; fwd; ff.
  Qed.
  Hint Rewrite -> lookup_remove_neq : maps.

  Theorem In_insert : forall V (k : K) (v : V) (m : Map K V),
    forall k',
      In k' (List.map fst (insert k v m)) ->
      In k' (List.map fst m) \/ k = k'.
  Proof.
    induction m; ff. 
    find_eapply_lem_hyp IHm; ff.
  Qed.

  Theorem NoDup_insert : forall V (k : K) (v : V) (m : Map K V),
    NoDup (List.map fst m) ->
    NoDup (List.map fst (insert k v m)).
  Proof.
    induction m; ff; eauto using NoDup.
    invc H; fwd.

    econstructor; ff.
    find_eapply_lem_hyp In_insert; ff.
  Qed.

  Theorem NoDup_mapify : forall V (l : Map K V),
    NoDup (List.map fst (mapify l)).
  Proof.
    induction l; ff; eauto using NoDup.
    find_eapply_lem_hyp NoDup_insert; ff.
  Qed.

  Theorem mapify_eq : forall V (m : Map K V) (k : K),
    lookup k (mapify m) = lookup k m.
  Proof.
    induction m; ff.
    ar with maps by ff.
    erewrite lookup_insert_neq; ff.
  Qed.
  Hint Rewrite -> mapify_eq : maps.

  Theorem lookup_app : forall V (l1 l2 : Map K V) (k : K),
    lookup k (l1 ++ l2) = 
      match lookup k l1 with
      | None => lookup k l2
      | Some v => Some v
      end.
  Proof.
    induction l1; ff;
    erewrite IHl1; ff.
  Qed.
  Hint Rewrite -> lookup_app : maps.

  Theorem lookup_eq : forall V (l1 l2 : Map K V) (k : K),
    lookup k (mapify (l1 ++ l2)) = 
      match lookup k l1 with
      | None => lookup k l2
      | Some v => Some v
      end.
  Proof.
    intros; unfold map_join; erewrite mapify_eq.
    ar with maps by ff.
  Qed.
  Hint Rewrite -> lookup_eq : maps.

  Theorem NoDup_map_join : forall V (m1 m2 : Map K V),
    NoDup (List.map fst (mapify (m1 ++ m2))).
  Proof.
    unfold map_join; ff; eapply NoDup_mapify.
  Qed.
  Hint Resolve NoDup_map_join : maps.

  Ltac2 dec_map_lookup () :=
    ff;
    repeat (match! goal with
      | [ h : context [ lookup ?_x (insert ?_x _ _) ] |- _ ] =>
        erewrite lookup_insert_eq in $h; ff
      | [ h : context [ lookup ?_x (insert ?_y _ _) ] |- _ ] =>
        erewrite lookup_insert_neq in $h; ff
      | [ h : context [lookup _ (map_Map _ _)] |- _ ] =>
        erewrite lookup_map_Map in $h; ff
      | [ |- context [ lookup ?_x (insert ?_x _ _) ]] =>
        erewrite lookup_insert_eq; ff
      | [ |- context [ lookup ?_x (insert ?_y _ _) ]] =>
        erewrite lookup_insert_neq; ff
      | [ |- context [lookup _ (map_Map _ _)] ] =>
        erewrite lookup_map_Map; ff
      end).

  Ltac2 Notation "dec_map_lookup" := dec_map_lookup ().

  Fixpoint map_union {V} (picker : V -> V -> V) (m1 m2 : Map K V) : Map K V :=
    match m1 with
    | [] => m2
    | (k, v) :: rest => 
      match lookup k m2 with
      | None => (* k ∉ m2, so just insert *)
        insert k v (map_union picker rest m2)
      | Some v2 => (* k ∈ m2, need to pick optimal value *)
        insert k (picker v v2) (map_union picker rest (remove k m2))
      end
    end.

  Theorem map_union_lookup {V} (picker : V -> V -> V) (m1 m2 : Map K V) (k : K) :
    lookup k (map_union picker m1 m2) = 
      match lookup k m1, lookup k m2 with
      | Some v1, Some v2 => Some (picker v1 v2)
      | Some v1, None => Some v1
      | None, Some v2 => Some v2
      | None, None => None
      end.
  Proof.
    generalizeEverythingElse m1.
    induction m1; ff; try (dec_map_lookup);
    erewrite IHm1; ff; try (dec_map_lookup); ff;
    erewrite lookup_remove_neq in *; ff.
  Qed.

  Fixpoint map_fold_left {V Acc} (f : Acc -> K -> V -> Acc) 
      (acc : Acc) (m : Map K V) : Acc :=
    match m with
    | [] => acc
    | (k, v) :: rest => map_fold_left f (f acc k v) rest
    end.


  Global Instance DecEq_Map {V} `{HV : DecEq V} : DecEq (Map K V).
  typeclasses_eauto.
  Defined.

End Maps.

Module MapNotations.

  (* Define a map scope *)
  Declare Scope map_scope.
  Notation "m '![' k ']'" := (lookup k m) (at level 2) : map_scope.
  Notation "m '![' k ':=' v ']'" := (insert k v m) (at level 2) : map_scope.
  Notation "m -- k" := (remove k m) (at level 50) : map_scope.
  Notation "m1 '+++' m2" := (map_join m1 m2) (at level 2) : map_scope.

End MapNotations.
Export MapNotations.