Require Import Arith.
Require Import ArithRing.
Fixpoint div2 (n:nat) : nat :=
  match n with 
  | 0 => 0
  | 1 => 0
  | S (S p) => S (div2 p)
  end.

Fixpoint mod2 (n:nat) : nat :=
  match n with 
  | 0 => 0
  | 1 => 1
  | S (S p) => mod2 p
  end.

Section mod_proof.
 Let P (n:nat) := (n = 2 * (div2 n) + mod2 n).

 Remark R : forall n : nat, P n /\ P (S n).
 Proof.
  simple induction n.
  unfold P; simpl; auto.
  intros n0 [H0 H1]; split.
  trivial.
  unfold P.
  pattern n0 at 1.
  rewrite H0; simpl; ring.
 Qed.

 Lemma div2_mod2 : forall n: nat, n = 2 * (div2 n) + mod2 n.
 Proof. 
  intro n; case (R n); auto.
 Qed.

End mod_proof.

