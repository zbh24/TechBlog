(* (C) Pierre Castéran , LaBRI, Universite Bordeaux 1,
                     Inria Futurs
Dictionaries (after Paulson : ML for the working programmer) *)

Require Export DecOrders.

(* Lexicographic ordering for lists *)

Module List_Order (D: DEC_ORDER) <: DEC_ORDER with Definition
  A := list D.A .

 Module M := More_Dec_Orders D.
 
 Definition A := list D.A .
 
 Fixpoint le (a b:A) {struct a}: Prop  :=
  match a, b with
  | nil, _ => True
  | x::l , y :: l'=> D.lt x y \/ x = y /\ le l l'
  | _ , _ => False
 end.

 Fixpoint lt (a b:A) {struct a}: Prop  :=
  match a, b with
  | x::l , y :: l'=> D.lt x y \/ x = y /\ lt l l'
  | nil , y::l' => True
  | _, _ => False
 end.

 
 Theorem ordered : order A le.
 Proof.
  split.
  unfold reflexive in |- *; intros.
  elim x; simpl.
  trivial.
  intros; tauto.
  unfold transitive in |- *. 
  simple induction x; simple  destruct y; simple destruct z; simpl; auto.
  contradiction.
  intros a1 l1 H0 H1.
  case H0 ; case H1.
  left; eapply M.lt_trans; eauto.
  intros [H2 H3]; rewrite H2; auto.
  intros H2 [H3 H4]; rewrite H3; auto. 
  intros [e H4][e' H5];rewrite e'; rewrite e; auto.
  right;split;eauto.
  unfold antisymmetric.
  induction x;destruct y; auto.
  inversion 2.
  inversion 1.
  inversion 1.
  inversion 1.
  absurd (D.lt a0 a0).
  apply M.lt_irreflexive.
  eapply M.lt_trans;eauto.
  fold le in H2.
  destruct H2. 
  rewrite H2.  
  inversion H.
  rewrite H2 in H0.
  absurd (D.lt a a).
  apply M.lt_irreflexive.
  auto.
  fold le in H4.
  case H4.
  intros e H5.
  rewrite (IHx y); auto.
  fold le in H0.
  destruct H0.
  rewrite H0.
  inversion 1.
  absurd (D.lt a0 a0).
  apply M.lt_irreflexive.
  auto.
  fold le in H3.
  destruct H3.
  rewrite (IHx y); auto.
 Qed.

 Theorem lt_le_weak : forall a b:A, lt a b -> le a b.
 Proof.
  induction a; destruct  b; simpl ; try tauto.
  intuition.
 Qed.

 Theorem lt_diff : forall a b:A, lt a b -> a <> b.
 Proof.
  induction a; destruct  b; simpl; intuition. 
  discriminate H0. 
  injection H0.
  intros.
  rewrite H2 in H1. 
  apply (M.lt_irreflexive a1);  auto.
  apply (IHa b).
  auto.
  injection H0; auto.
 Qed.


 Theorem le_lt_or_eq : forall a b:A, le a b -> lt a b \/ a = b.
 Proof.
  induction a; destruct b; simpl; intuition.
  case (IHa _ H1).
  rewrite H; auto. 
  rewrite H; auto.
  case (IHa _ H1); auto.
  destruct 1; auto. 
 Qed.


 Definition lt_eq_lt_dec : forall a b:A, {lt a b} + {a = b} + {lt b a}.
  induction a; simpl ; auto.
  destruct b; simpl; auto.
  destruct b; simpl; auto.
  case (D.lt_eq_lt_dec a a1); case (IHa b); simpl; auto.
  destruct 1 ; auto.
  destruct 1; auto.
  destruct 1;auto.
  rewrite e; rewrite e0; auto.
  destruct 2; auto.
 Defined.

End List_Order. 



