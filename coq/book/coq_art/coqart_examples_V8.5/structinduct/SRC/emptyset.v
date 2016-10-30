Check Empty_set.

Theorem all_equal : forall x y : Empty_set, x = y.
Proof.
 simple destruct x.
Qed.


Theorem all_diff : forall x y : Empty_set, x <> y.
Proof.
 simple destruct x.
Qed.

