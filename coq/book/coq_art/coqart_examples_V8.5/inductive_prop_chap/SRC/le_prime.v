Require Import Arith.

Inductive le' : nat -> nat -> Prop :=
  | le'_0_p : forall p:nat, le' 0 p
  | le'_Sn_Sp : forall n p:nat, le' n p -> le' (S n) (S p).

Hint Resolve le'_0_p le'_Sn_Sp.

Lemma le'_n : forall n : nat, le' n n.
Proof.
 simple induction n; auto.
Qed.

Lemma le'_n_Sp : forall n p : nat, le' n p -> le' n (S p).
Proof.
  simple induction n.
  auto.
  intros n0 Hn0 p Hp.
  inversion_clear Hp.
  auto.
Qed.
Hint Resolve le'_n le'_n_Sp.

Lemma le_le' : forall n p: nat, le n p -> le' n p.
Proof.
 simple induction 1; auto with arith.
Qed.

Lemma le'_le : forall n p: nat, le' n p -> le n p.
Proof.
 simple induction n; auto with arith.
 intros n0 Hn0 p; case p.
 inversion 1.
 inversion 1.
 auto with arith.
Qed.

