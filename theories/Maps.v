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
    induction m; ff.
  Qed.
  Hint Rewrite -> lookup_remove_neq : maps.

  Theorem In_insert : forall V (k : K) (v : V) (m : Map K V),
    forall k',
      In k' (List.map fst (insert k v m)) ->
      In k' (List.map fst m) \/ k = k'.
  Proof.
    induction m; ff a.
  Qed.

  Theorem NoDup_insert : forall V (k : K) (v : V) (m : Map K V),
    NoDup (List.map fst m) ->
    NoDup (List.map fst (insert k v m)).
  Proof.
    induction m; ff r; inv H;
    econstructor; ff r;
    find_eapply_lem_hyp In_insert; ff r.
  Qed.

  Theorem NoDup_mapify : forall V (l : Map K V),
    NoDup (List.map fst (mapify l)).
  Proof.
    induction l; ff r; try econstructor;
    find_eapply_lem_hyp NoDup_insert; ff r.
  Qed.

  Theorem mapify_eq : forall V (m : Map K V) (k : K),
    lookup k (mapify m) = lookup k m.
  Proof.
    induction m; ff a, r; 
    ar with maps by ff;
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
    induction l1; ff a, r; ar with maps by ff.
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