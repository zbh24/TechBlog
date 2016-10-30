Require Import Arith.

Fixpoint div3 (n:nat): nat :=
  match n with 0 => 0 | 1 => 0 | 2 => 0 |
               (S (S (S p))) => (S (div3 p))
          end.

Section div3_proof.
 Let P (n:nat) := div3 n <= n.

 Remark P_ok : forall n : nat, P n /\ P (S n) /\ P (S (S n)).
 Proof.
  simple induction n.
  unfold P; simpl ; auto.
  intros n0 [H1 [H2 H3]].
  repeat split; auto.
  unfold P; simpl; auto with arith.
Qed.

 Lemma div3_le : forall n : nat, div3 n <= n.
 Proof.
  intro n; case (P_ok n); auto.
 Qed.

End div3_proof.

