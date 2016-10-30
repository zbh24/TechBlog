Check nat_rec.

Definition direct_plus :=
  nat_rec (fun n:nat => nat -> nat) (fun p:nat => p)
    (fun (n':nat) (plus_n':nat -> nat) (p:nat) => S (plus_n' p)).

Require Import Arith.

Theorem my_solution_correct : forall n p:nat, n + p = direct_plus n p.
Proof.
 simple induction n; simple induction p; simpl in |- *; auto with arith.
Qed.


