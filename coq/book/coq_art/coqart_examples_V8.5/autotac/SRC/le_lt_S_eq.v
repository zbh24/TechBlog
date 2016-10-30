Require Import Omega.
Lemma le_lt_S_eq : forall n p:nat, n <= p -> p < S n -> n = p.
Proof.
 intros; omega.
Qed.