From Coq Require Export 
  String 
  EquivDec 
  Program.Utils 
  Program.Basics 
  Setoid
  List
  Lia.
Export ListNotations.

From RocqCandy Require Export Stringifiable Tactics.

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

Global Instance EqDec_string : EqDec string eq := string_dec.
