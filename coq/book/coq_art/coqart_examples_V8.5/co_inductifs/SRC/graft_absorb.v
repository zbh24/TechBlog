Require Export LTree_bisimilar.

Set Implicit Arguments.

Theorem graft_absorb : forall (A:Set)(t1 t2: LTree A),
                       EveryInf t1 ->
                       LTree_bisimilar t1 (graft t1 t2).
Proof.
 cofix.
 intros A t1 t2; case t1.
 inversion_clear 1.
 intros a l l0 H ; rewrite graft_unfold2.
 inversion_clear H.
 right; auto.
Qed.

