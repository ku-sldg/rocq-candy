(*
This allows lifting between all of our defined monads.
*)

From RocqCandy.Monads Require Import ResultMonad StateMonad ConfigMonad.

(* Result Lifts *)
Definition lift_result_to_state {St A E} (r : Result A E)
    : State St (Result A E) :=
  ret r.

Definition lift_result_to_config {Cfg A} (r : Result A unit) 
    : Config Cfg (Result A unit) :=
  done r.

(* State Lifts *)
Definition lift_state_to_config {Cfg St A} (m : State St A) 
    : Config Cfg (State St A) :=
  done m.

Definition lift_state_to_result {St A E} (m : State St A) (s : St) 
    : Result (State St A) E :=
  res m.

(* Config Lifts *)
Definition lift_config_to_state {Cfg St A} (m : Config Cfg A) 
    : State St (Config Cfg A) :=
  ret m.

Definition lift_config_to_result {Cfg A} (m : Config Cfg A) 
    : Result (Config Cfg A) unit :=
  res m.

(* Documentation: To compose monads, use these explicit lift functions to embed computations from an inner monad into an outer monad. *)

Module Export LiftNotations.
  (* Result lifts *)
  Notation "'↑sr' r" := (lift_result_to_state r) (at level 0).
  Notation "'↑cr' r" := (lift_result_to_config r) (at level 0).
  (* State lifts *)
  Notation "'↑cs' m" := (lift_state_to_config m) (at level 0).
  Notation "'↑rs' m" := (lift_state_to_result m) (at level 0).
  (* Config lifts *)
  Notation "'↑sc' m" := (lift_config_to_state m) (at level 0).
  Notation "'↑rc' m" := (lift_config_to_result m) (at level 0).
End LiftNotations.
Export LiftNotations.
