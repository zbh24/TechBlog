
Unset Implicit Arguments.

Definition compose (A:Set) (g f:A -> A) (x:A) := g (f x).

Definition thrice (A:Set) (f:A -> A) := compose A f (compose A f f).

Eval compute in (thrice _ (thrice _) S 0).

Check (thrice _ (thrice _) S 0).
