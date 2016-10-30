Require Import Arith.

Inductive even : nat -> Prop :=
  | O_even : even 0
  | plus_2_even : forall n:nat, even n -> even (S (S n)).


Hint Resolve O_even plus_2_even.

Fixpoint mult2 (n:nat) : nat :=
  match n with
  | O => 0
  | S p => S (S (mult2 p))
  end.

Lemma mult2_even : forall n:nat, even (mult2 n).
Proof. 
 induction n; simpl; auto.
Qed.

Theorem sum_even : forall n p:nat, even n -> even p -> even (n + p).
Proof.
 intros n p Heven_n; elim Heven_n; simpl; auto.
Qed.

Hint Resolve sum_even.

Lemma square_even : forall n:nat, even n -> even (n * n).
Proof.
 intros n Hn; elim Hn; simpl; auto.
 Check mult_comm.
 intros n0 H0 H1; rewrite (mult_comm n0 (S (S n0))).
 simpl.
 auto.
 right.
 apply sum_even; auto.
Qed.


Lemma even_mult2 : forall n:nat, even n -> (exists p, n = mult2 p).
Proof.
 induction 1.
 exists 0;simpl;auto.
 case IHeven; intros p Hp.
 exists (S p); simpl; auto.
Qed.

