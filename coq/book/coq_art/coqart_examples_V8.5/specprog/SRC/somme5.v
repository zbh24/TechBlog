Require Import ZArith.

Open Scope Z_scope.

Definition sum5 (z1 z2 z3 z4 z5:Z):= z1 + z2 + z3 + z4 + z5.


(* some equivalent notation *)

Definition sum5' := fun z1 z2 z3 z4 z5:Z => z1 + z2 + z3 + z4 + z5.

Eval compute in (sum5' 2 (-5) 8 789 135).


(* without writing any abstraction *)

Section Sum5.
 Variables z1 z2 z3 z4 z5 : Z.

 Definition sum5'' := z1 + z2 + z3 + z4 + z5.
End Sum5.

Eval compute in (sum5'' 1 1 1 1 1).