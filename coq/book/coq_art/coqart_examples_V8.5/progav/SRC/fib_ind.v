Require Import Arith.

Lemma fib_ind :
 forall P:nat -> Prop,
   P 0 ->
   P 1 -> 
  (forall n:nat, P n -> P (S n) -> P (S (S n))) ->
  forall n:nat, P n.
Proof.
 intros P H0 H1 HSSn n.
 cut (P n /\ P (S n)).
 tauto.
 elim n.
 split; auto.
 intros n0 Hn0; case Hn0; auto.
Qed.


Fixpoint fib (n:nat) : nat :=
  match n with
  | O => 1
  | S O => 1
  | S (S p as q) => fib p + fib q
  end.

Lemma fib_SSn : forall n:nat, fib (S (S n)) = fib n + fib (S n).
Proof.
 simpl; auto.
Qed.

Require Import Omega.
Require Import ArithRing.
Require Arith.
Lemma fib_SSn_p :
 forall n p:nat, fib (S (S p) + n) = fib (S n) * fib (S p) + fib n * fib p.
Proof.
 intro n; elim n using fib_ind.
 simpl.
 intros; repeat rewrite  plus_0_r.
 rewrite plus_comm; auto.
 intro p; replace (S (S p) + 1) with (S (S (S p))).
 rewrite (fib_SSn (S p)).
 simpl (fib 2); simpl (fib 1).
 rewrite (fib_SSn p).
 ring.
 rewrite plus_comm; simpl; auto.
 intros n0 H0 H1 p.
 replace (S (S p) + S (S n0)) with (S (S (S (S p) + n0))).
 2: omega.
 rewrite (fib_SSn (S (S p) + n0)).
 rewrite H0.
 replace (S (S (S p) + n0)) with (S (S p) + S n0).
 2: omega.
 rewrite H1.
 rewrite (fib_SSn (S n0)).
 rewrite (fib_SSn n0).
 repeat rewrite mult_plus_distr.
 ring.
Qed.

