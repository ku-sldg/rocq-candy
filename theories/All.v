From Coq Require Export 
  String 
  EquivDec 
  Program.Utils 
  Program.Basics 
  Setoid
  List
  Lia
  ZArith.
Export ListNotations.

From RocqCandy Require Export Stringifiable Tactics EqClass.

(* Exporting finite assoc list based maps *)
From ExtLib Require Export RelDec Maps FMapAList.
Export MonadNotation.

Definition FMap K V `{RelDec K} := alist K V.
Global Instance Map_FMap K V `{RelDec K} : Map K V (FMap K V).
eapply Map_alist; eauto.
Defined.

Global Instance RelDec_EqDec T f `{EqDec T f} : RelDec f := {
  rel_dec := fun x y => if equiv_dec x y then true else false
}.

Global Instance RelDec_EqClass T (f : T -> T -> Prop) `{EqClass T} : RelDec f := {
  rel_dec := fun x y => eqb x y
}.

(* Common EqDec Instances we may need *)
Global Instance EqDec_string : EqDec string eq := string_dec.
Global Instance EqDec_nat : EqDec nat eq := Peano_dec.eq_nat_dec.
Global Instance EqDec_Z : EqDec Z eq := Z.eq_dec.
