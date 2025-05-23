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

From RocqCandy Require Export Stringifiable Tactics EqClass ResultMonad.

Global Instance RelDec_EqDec T f `{EqDec T f} : RelDec f := {
  rel_dec := fun x y => if equiv_dec x y then true else false
}.

Global Instance RelDec_EqClass T `{EqClass T} : @RelDec T eq := {
  rel_dec := fun x y => eqb x y
}.

Definition FMap K V `{EqClass K} := alist K V.
Global Instance Map_FMap K V `{EqClass K} : Map K V (FMap K V).
eapply Map_alist; eauto.
typeclasses_eauto.
Defined.

(* Common EqDec Instances we may need *)
Global Instance EqDec_string : EqDec string eq := string_dec.
Global Instance EqDec_nat : EqDec nat eq := Peano_dec.eq_nat_dec.
Global Instance EqDec_Z : EqDec Z eq := Z.eq_dec.

Global Instance EqClass_Z : EqClass Z := {
  eqb := Z.eqb;
  eqb_eq := Z.eqb_eq
}.
