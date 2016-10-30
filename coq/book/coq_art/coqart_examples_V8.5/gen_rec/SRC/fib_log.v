Require Export Arith.
Require Export ArithRing.
Require Export Wf_nat.
Add LoadPath "../../progav/SRC/".
(* The preliminary theorems are already in the exercise fib_positive. *)
Require Export fib_positive.
 
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
 
Definition fib_log_F:
 forall (x : nat),
 (forall (y : nat),
  y < x ->  ({u : nat & {v : nat | u = fib y /\ v = fib (S y)}})) ->
  ({u : nat & {v : nat | u = fib x /\ v = fib (S x)}}).
intros [|x'].
intros _.
exists 1; exists 1; auto.
destruct (div2_spec (S x')) as [[half_sx' Heq]|[half_x' Heq]]; intros fib_log.
destruct (fib_log half_sx' (half_smaller0 _ _ Heq)) as [u [v [Heq1 Heq2]]].
rewrite <- Heq.
exists (u * u + (v - u) * (v - u)).
exists ((2 * u) * v - u * u).
rewrite Heq1; rewrite Heq2.
split.
replace (S half_sx') with (half_sx' + 1).
rewrite <- fib_2n.
trivial.
ring.
replace (S half_sx') with (half_sx' + 1).
rewrite <- fib_2n_plus_1.
replace (2 * half_sx' + 1) with (S (2 * half_sx')).
trivial.
ring.
ring.
destruct (fib_log half_x' (half_smaller1 _ _ Heq)) as [u [v [Heq1 Heq2]]].
rewrite <- Heq.
exists ((2 * u) * v - u * u).
exists (v * v + u * u).
rewrite Heq1; rewrite Heq2.
split.
replace (S half_x') with (half_x' + 1).
rewrite <- fib_2n_plus_1.
trivial.
ring.
replace (S half_x') with (half_x' + 1).
rewrite <- fib_2n_plus_2.
trivial.
ring.
Qed.
 
Definition fib_log :
  forall (x : nat),  ({u : nat & {v : nat | u = fib x /\ v = fib (S x)}}) :=
   well_founded_induction
    lt_wf (fun x => {u : nat & {v : nat | u = fib x /\ v = fib (S x)}})
    fib_log_F.
