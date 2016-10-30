(* (c) P. Casteran *)

Require Import Arith.
Fixpoint sum_n (n:nat) : nat :=
  match n with
  | O => 0
  | S p => S p + sum_n p
  end.

Require Import ArithRing.

Theorem sum_closed_form : forall n:nat, 2 * sum_n n = n * S n.
Proof.
 induction n. 
 simpl; trivial.
 simpl (sum_n (S n)).
 simpl (S n * S (S n)).
 ring_simplify.
   ring_simplify. (* for V81gamma *)
 rewrite IHn.
 ring.
Qed.

Theorem sum_n_le_n : forall n:nat, n <= sum_n n.
Proof.
 simple induction n.
 auto with arith.
 intros n0 Hn0; simpl.
 auto with arith.
Qed.

