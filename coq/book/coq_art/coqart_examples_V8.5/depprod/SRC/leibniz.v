Require Import Relations.
Section leibniz.
 Variable A : Set.
 
 Set Implicit Arguments.

 Definition leibniz (a b:A) : Prop := forall P:A -> Prop, P a -> P b.

 Theorem leibniz_sym : symmetric A leibniz.
 Proof.
  unfold symmetric, leibniz; intros a b H Q.
  apply H; trivial.
 Qed.

 Theorem leibniz_refl : reflexive A leibniz. 
 Proof.
  unfold reflexive, leibniz; auto.
 Qed.



 Theorem leibniz_trans : transitive A leibniz.
 Proof.
  unfold transitive.
  intros x y z Hxy Hyz; unfold leibniz; intros.
  apply Hyz.
  apply Hxy; assumption.
 Qed.




 Hint Resolve leibniz_trans leibniz_sym leibniz_refl: sets. 

 Theorem leibniz_equiv : equiv A leibniz.
 Proof.
  unfold equiv; auto with sets.
 Qed.


 Theorem leibniz_least :
  forall R:relation A, reflexive A R -> inclusion A leibniz R.
 Proof.
  unfold inclusion, leibniz; intros R H x y H0.
  apply H0.
  apply H.
 Qed.


 Theorem leibniz_eq : forall a b:A, leibniz a b -> a = b.
 Proof.
  intros.
  apply H.
  trivial.
 Qed.

 Theorem eq_leibniz : forall a b:A, a = b -> leibniz a b.
 Proof.
  intros a b e; rewrite e; unfold leibniz; auto.
 Qed.

 Theorem leibniz_ind :
  forall (x:A) (P:A -> Prop), P x -> forall y:A, leibniz x y -> P y.
 Proof.
  intros.
  apply H0.
  assumption.
 Qed.

 Set Strict Implicit.
Unset Implicit Arguments.
End leibniz.

