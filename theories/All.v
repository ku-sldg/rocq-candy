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

(* Exporting finite assoc list based maps *)
From ExtLib Require Export RelDec Maps FMapAList.

From RocqCandy Require Export Stringifiable Tactics DecEq ResultMonad.

Global Instance RelDec_EqDec T f `{EqDec T f} : RelDec f := {
  rel_dec := fun x y => if equiv_dec x y then true else false
}.

Global Instance RelDec_EqClass T `{DecEq T} : @RelDec T eq := {
  rel_dec := fun x y => if dec_eq x y then true else false
}.

Definition FMap K V `{DecEq K} := alist K V.
Global Instance Map_FMap K V `{DecEq K} : Map K V (FMap K V).
eapply Map_alist; eauto.
typeclasses_eauto.
Defined.

(* Common EqDec Instances we may need *)
Global Instance EqDec_string : EqDec string eq := string_dec.
Global Instance EqDec_nat : EqDec nat eq := Peano_dec.eq_nat_dec.
Global Instance EqDec_Z : EqDec Z eq := Z.eq_dec.

Global Instance DecEq_Z : DecEq Z := {
  dec_eq := Z.eq_dec
}.
