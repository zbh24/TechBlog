Require Import ZArith.

Definition pos_even_bool (p:positive) : bool :=
  match p with
  | xO _ => true
  | _ => false
  end.

(* some examples *)


Eval compute in (pos_even_bool 326%positive).

Eval compute in (pos_even_bool 3261%positive).

