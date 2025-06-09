From Stdlib Require Export 
  String 
  EquivDec 
  Program.Utils 
  Program.Basics 
  Setoid
  List
  Lia
  ZArith.
Export ListNotations.

From RocqCandy Require Export Stringifiable Tactics DecEq ResultMonad Maps.

(* Common EqDec Instances we may need *)
Global Instance EqDec_string : EqDec string eq := string_dec.
Global Instance EqDec_nat : EqDec nat eq := Peano_dec.eq_nat_dec.
Global Instance EqDec_Z : EqDec Z eq := Z.eq_dec.

Global Instance DecEq_Z : DecEq Z := {
  dec_eq := Z.eq_dec
}.
