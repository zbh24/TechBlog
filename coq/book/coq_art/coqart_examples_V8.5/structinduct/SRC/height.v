Require Export ZArith.

Inductive htree (A:Set) : nat->Set :=
 | hleaf : A->htree A 0
 | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).


Fixpoint make_htree (n:nat): htree Z n :=
  match n return htree Z n with
    0 => hleaf Z 0%Z
  | S p => hnode Z p  0%Z (make_htree p) (make_htree p)
  end.
