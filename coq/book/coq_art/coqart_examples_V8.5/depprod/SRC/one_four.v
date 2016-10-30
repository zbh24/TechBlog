Theorem abcd_c : forall (A:Set) (a b c d:A), a = c \/ b = c \/ c = c \/ d = c.
Proof.
 intros A a b c d; right; right; left; reflexivity.
Qed.