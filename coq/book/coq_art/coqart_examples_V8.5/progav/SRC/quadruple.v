Theorem induc4 : forall P: nat-> Prop,
                 P 0 -> P 1 -> P 2 -> P 3 ->
                 (forall p, P p -> P (S (S (S (S p))))) ->
                 forall n, P n.
Proof.
 intros P H0 H1 H2 H3 H.
 cut (forall n, (P n /\ P (S n) /\ P (S (S n)) /\ P (S (S (S n))))).
 intros H4 n; case (H4 n); auto.
 induction n.
 repeat split; auto.
 intuition.  
Qed.

