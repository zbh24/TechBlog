Require Import ZArith.

Open Scope Z_scope.

Definition pol := fun x:Z => 2*x*x + 3*x +3.
Reset pol.

Definition pol (x:Z) : Z := 2*x*x + 3*x +3.

Eval compute in (pol (-6)).
Eval compute in (pol 1024).

