Require Import Arith.

Definition lt_3 (n:nat) : bool :=
  match n with
  | O => true
  | 1 => true
  | 2 => true
  | _ => false
  end.

Eval compute in (lt_3 45).

Eval compute in (lt_3 2).

Print lt_3.



