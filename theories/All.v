From Stdlib Require Export 
  String 
  EquivDec 
  Program.Utils 
  Program.Basics 
  Setoid
  Lia
  ZArith.

From RocqCandy Require Export 
  Stringifiable 
  Tactics 
  DecEq 
  Maps 
  SPropTools 
  IndSchemes.
From RocqCandy.Monads Require Export 
  ResultMonad 
  StateMonad 
  ConfigMonad
  MonadTransformers.

(* Notation for lists *)
From Stdlib Require Export List.
Export ListNotations.

(* Common EqDec Instances we may need *)
Global Instance EqDec_string : EqDec string eq := string_dec.
Global Instance EqDec_nat : EqDec nat eq := Peano_dec.eq_nat_dec.
Global Instance EqDec_Z : EqDec Z eq := Z.eq_dec.

Global Instance DecEq_Z : DecEq Z := {
  dec_eq := Z.eq_dec
}.
