Require Import Coinduc.

Require Import Classical.

Lemma Not_Infinite_Finite :
  forall (A:Set) (l:LList A),
   ~ Infinite l -> Finite l.
Proof.
  intros A l H.
  case (classic (Finite l)).
  trivial.
  intro; elim H ; apply Not_Finite_Infinite ; trivial.
Qed.

Lemma Finite_or_Infinite :
  forall (A:Set)(l:LList A), Finite l \/ Infinite l. 
Proof.
  intros A l; case (classic (Finite l)).
  auto.
  right; apply Not_Finite_Infinite ; trivial.
Qed.

