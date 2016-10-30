Require Import Arith.

Fixpoint two_power (n:nat) : nat :=
  match n with
  | O => 1
  | S p => 2 * two_power p
  end.

Eval compute in (two_power 5).

