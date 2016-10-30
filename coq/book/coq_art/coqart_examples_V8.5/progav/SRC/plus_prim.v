Require Import Arith.

Fixpoint plus' (n m:nat){struct m} : nat :=
  match m with O => n | S p => S (plus' n p) 
  end.


Lemma plus'_assoc : forall n m p, plus' n (plus' m p)= plus' (plus' n m) p.
Proof.
 intros n m p ; elim p; simpl; auto. 
Qed.

