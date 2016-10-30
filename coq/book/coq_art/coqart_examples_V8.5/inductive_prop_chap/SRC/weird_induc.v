Require Import Arith.
Require Import Omega.

Section weird_induc_proof.
 Variable P : nat -> Prop.
 Variable f : nat -> nat.
 
 Hypothesis f_strict_mono : forall n p:nat, n < p -> f n < f p.
 Hypothesis f_O : 0 < f 0.
 
 Hypothesis P0 : P 0.
 Hypothesis P_Sn_n : forall n:nat, P (S n) -> P n.
 Hypothesis f_P : forall n:nat, P n -> P (f n).
 
 Fixpoint iterate (A:Set) (f:A -> A) (n:nat) (x:A) {struct n} : A :=
   match n with
   | O => x
   | S p => f (iterate A f p x)
   end.




 Lemma i_f_i : forall i:nat, i <= iterate _ f i 0.
 Proof.
  intro i; elim i.
  auto with arith.
  intros n Hn.
  cut (iterate _ f n 0 < iterate _ f (S n) 0).
  intros.
  clear P_Sn_n f_strict_mono f_O f_P.
  omega.
  elim n; simpl; auto.
 Qed.

 Lemma f_le : forall i j:nat, i <= j -> P j -> P i.
 Proof.
  intros i j H; elim H; auto.
 Qed.

 Lemma p_iter_f : forall i:nat, P (iterate _ f i 0).
 Proof.
  intro i; elim i; simpl; auto.
 Qed.

 Theorem weird_induc : forall n:nat, P n.
 Proof.
  intro n.
  eapply f_le.
  apply i_f_i.
  apply p_iter_f.
 Qed.

End weird_induc_proof.

Check weird_induc.
 