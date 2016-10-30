Require Export Tree_Inf.
Require Relations.

Set Implicit Arguments.

Section LTree_bisimilar_def.
 Variable A:Set.

(* An extensional equality on (LTree A) *)
 CoInductive LTree_bisimilar : (LTree A)->(LTree A)->Prop :=
  LTree_bisimilar_leaf : LTree_bisimilar LLeaf LLeaf
| LTree_bisimilar_bin : forall (a:A) (t1 t'1 t2 t'2 : LTree A),
                LTree_bisimilar t1 t'1 ->
                LTree_bisimilar t2 t'2 ->
                LTree_bisimilar (LBin a t1 t2) (LBin a t'1 t'2).

Require Import Relations.

Lemma LTree_bisimilar_refl : (reflexive _ LTree_bisimilar).
Proof.
 unfold reflexive; cofix.
 intro a; case a ; constructor; auto.
Qed.

Lemma LTree_bisimilar_sym : (symmetric _ LTree_bisimilar).
Proof.
 unfold symmetric; cofix.
 intros x y; case x; case y.
 constructor.
 inversion_clear 1.
 inversion_clear 1.
 inversion_clear 1.
 constructor; auto.
Qed.

Lemma LTree_bisimilar_trans : (transitive _ LTree_bisimilar).
Proof.
 unfold transitive; cofix.
 intros x y z ; case x; case y.
 case z;[auto | inversion_clear 2].
 inversion_clear 1.
 inversion_clear 1.
 inversion_clear 1.
 case z; inversion_clear 1. 
 constructor; eauto.
Qed.

 Theorem LTree_bisimilar_label : 
   forall (p:path) (t t': LTree A),
          LTree_bisimilar t t' ->
          LTree_label t p = LTree_label t' p.
 Proof.
  simple induction p.
  intros t t'; case t; case t'.
  simpl; auto.
  inversion_clear 1.
  inversion_clear 1.
  inversion_clear 1; simpl; auto.
   intros a l;case a; intros H t t'; case t; case t'.
  auto.
  inversion_clear 1.
  inversion_clear 1.
  inversion_clear 1; simpl.
  repeat  rewrite LTree_label_rw0.
  auto.
  repeat  rewrite LTree_label_rw1; auto.
  inversion_clear 1.
  inversion_clear 1.
  inversion_clear 1.
  repeat  rewrite LTree_label_rw1; auto.
 Qed.


 Theorem label_LTree_bisimilar :  forall t t': LTree A, 
                          (forall p:path, LTree_label t p = LTree_label t' p)->
                          LTree_bisimilar t t'.
 Proof.
  cofix.
  intros t t'; case t; case t'.
  constructor.
  intros a l l0 H.
  generalize (H nil ).
  simpl.
  unfold LTree_label; simpl.  
  discriminate 1.  
  intros a l l0 H.
  generalize (H nil).
  simpl.
  unfold LTree_label; simpl.  
  discriminate 1.  
  intros a l l0 a0 t1 t2 H.
  cut (a = a0).
  simple induction 1; constructor.
  apply label_LTree_bisimilar. 
  intro p ;  generalize (H (cons d0 p)).
  repeat rewrite LTree_label_rw0; auto.
  apply label_LTree_bisimilar. 
  intro p ; generalize (H (cons d1 p)).
  repeat rewrite LTree_label_rw1; auto.
  generalize (H nil).
  repeat rewrite LTree_label_rw_root_bin; auto.
  injection 1;auto.
 Qed.

End LTree_bisimilar_def.
