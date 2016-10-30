Check (forall A:Set, A -> A).

Definition id (A:Set) (a:A) : A := a.

Check (forall A B:Set, (A -> A -> B) -> A -> B).

Definition diag (A B:Set) (f:A -> A -> B) (a:A) : B := f a a.


Check (forall A B C:Set, (A -> B -> C) -> B -> A -> C).
 
Definition permute (A B C:Set) (f:A -> B -> C) (b:B) (a:A) : C := f a b.

Require Import ZArith.

Check (forall A:Set, (nat -> A) -> Z -> A).

Definition f_nat_Z (A:Set) (f:nat -> A) (z:Z) : A := f (Zabs_nat z).
