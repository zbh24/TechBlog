
Theorem eq_trans : forall (A:Set) (a b c:A), a = b -> b = c -> a = c.
Proof.
 intros A a b c H.
 pattern b.
 apply eq_ind with A a.
 trivial.
 assumption.
Qed.

Theorem eq_trans' : forall (A:Set) (a b c:A), a = b -> b = c -> a = c.
Proof.
 intros A a b c H; rewrite H.
 trivial.
Qed.


Theorem eq_trans'' : forall (A:Set) (a b c:A), a = b -> b = c -> a = c.
Proof.
 intros A a b c H H0.
 rewrite H; assumption.
Qed.

