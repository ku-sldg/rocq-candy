From Stdlib Require Export String.
Local Open Scope string_scope.
From RocqCandy Require Import Tactics ResultMonad.
Import Result.Notation.

Class Stringifiable (A : Type) := {
  to_string                   : A -> string ;
  from_string                 : string -> (Result.t A string) ;
  canonical_stringification   : forall a, 
    from_string (to_string a) = ret a 
}.

Global Instance Stringifiable_string : Stringifiable string := {
  to_string := fun s => s;
  from_string := fun s => ret s;
  canonical_stringification := fun s => eq_refl;
}.

Global Instance Stringifiable_bool : Stringifiable bool := {
  to_string := fun b => if b then "true" else "false";
  from_string := fun s => 
                  if String.eqb s "true" 
                  then ret true
                  else if String.eqb s "false" 
                  then ret false
                  else raise "Not a boolean";
  canonical_stringification := fun b =>
                                  match b with
                                  | true => eq_refl
                                  | false => eq_refl
                                  end;
}.

