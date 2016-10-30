
Require Import Arith.

Fixpoint fib (n:nat) : nat :=
  match n with
  | O => 1
  | S O => 1
  | S (S p as q) => fib p + fib q
  end.


Eval compute in (fib 10).


Lemma fib_SSn : forall n:nat, fib (S (S n)) = fib n + fib (S n).
Proof.
 simpl; auto.
Qed.



(* This function computes the pair (fib n, fib (S n)) *)

Fixpoint fib_pair (n:nat) : nat * nat :=
  match n with
  | O => (1, 1)
  | S p => match fib_pair p with
           | (x, y) => (y, x + y)
           end
  end.

Definition linear_fib (n:nat) := fst (fib_pair n).


Lemma fib_pair_correct : forall n:nat, fib_pair n = (fib n, fib (S n)).
Proof.
 intro n; elim n; simpl.
 auto.
 intros n0 Hrec; rewrite Hrec; auto.
Qed.

Theorem linear_fib_correct : forall n:nat, linear_fib n = fib n.
Proof. 
 unfold linear_fib; intro n; rewrite fib_pair_correct; simpl; auto.
Qed.
