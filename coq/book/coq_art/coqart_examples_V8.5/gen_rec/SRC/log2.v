Require Export Arith.
Require Export ArithRing.
Require Export Omega.
 
Fixpoint two_power (n : nat) : nat :=
 match n with 0 => 1 | S p => 2 * two_power p end.
 
Theorem div2_rec:
 forall (P : nat ->  Set),
 P 0 -> P 1 -> (forall n, P n ->  P (S (S n))) -> forall (n : nat),  P n.
Proof.
intros P H0 H1 Hrec n; assert (P n * P (S n))%type.
elim n; intuition.
intuition.
Qed.
 
Theorem div2_spec:
 forall n,  ({x : nat | 2 * x = n}) + ({x : nat | 2 * x + 1 = n}).
intros n; elim n  using div2_rec.
left; exists 0; trivial.
right; exists 0; trivial.
intros p [[x Heq]|[x Heq]].
left; exists (S x); rewrite <- Heq; ring.
right; exists (S x); rewrite <- Heq; ring.
Qed.
 
Theorem half_smaller0: forall n x, 2 * x = S n ->  (x < S n).
Proof.
intros; omega.
Qed.
 
Theorem half_smaller1: forall n x, 2 * x + 1 = n ->  (x < n).
Proof.
intros; omega.
Qed.
 
Definition log2_F:
 forall (n : nat),
 (forall (y : nat),
  y < n -> y <> 0 ->  ({p : nat | two_power p <= y /\ y < two_power (p + 1)})) ->
 n <> 0 ->  ({p : nat | two_power p <= n /\ n < two_power (p + 1)}).
intros n; case n.
intros log2 Hn0; elim Hn0; trivial.
intros n' log2 _.
elim (div2_spec (S n')).
intros [x]; case x.
simpl; intros; discriminate.
intros x' Heqx'; assert (Hn0: S x' <> 0).
auto with arith.
destruct (log2 (S x') (half_smaller0 _ _ Heqx') Hn0) as [v Heqv].
exists (S v); simpl.
rewrite <- Heqx'.
omega.
intros [x]; case x.
simpl.
intros Heq; rewrite <- Heq; exists 0.
simpl; auto with arith.
intros x' Heqx'; assert (Hn0: S x' <> 0).
auto with arith.
destruct (log2 (S x') (half_smaller1 _ _ Heqx') Hn0) as [v Heqv].
exists (S v); rewrite <- Heqx'.
simpl; omega.
Qed.
