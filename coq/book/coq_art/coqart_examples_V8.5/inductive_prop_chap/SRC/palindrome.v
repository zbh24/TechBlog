Require Import List.
Require Import Arith.

Section mirror.

 Variable A : Set.
 Set Implicit Arguments.


 Inductive remove_last (a:A) : list A -> list A -> Prop :=
   | remove_last_hd : remove_last a (a :: nil) nil
   | remove_last_tl :
       forall (b:A) (l m:list A),
         remove_last a l m -> remove_last a (b :: l) (b :: m). 

 Inductive palindromic : list A -> Prop :=
   | empty_pal : palindromic nil
   | single_pal : forall a:A, palindromic (a :: nil)
   | cons_pal :
       forall (a:A) (l m:list A),
         palindromic l -> remove_last a m l -> palindromic (a :: m).
 
 Hint Resolve empty_pal single_pal cons_pal remove_last_hd remove_last_tl.

 Lemma ababa : forall a b:A, palindromic (a :: b :: a :: b :: a :: nil).
 Proof.
  eauto 7.
 Qed.


(* more about palindromes *)

Lemma remove_last_inv :
 forall (a:A) (l m:list A), remove_last a m l -> m = l ++ a :: nil.
Proof.
 intros a l m H; elim H; simpl; auto with datatypes.
 intros b l0 m0 H0 e; rewrite e; trivial.
Qed.

Lemma rev_app : forall l m:list A, rev (l ++ m) = rev m ++ rev l.
Proof.
 intros l m; elim l; simpl; auto with datatypes.
 intros a l0 H0.
 rewrite ass_app; rewrite H0; auto.
Qed.

Lemma palindromic_rev : forall l:list A, palindromic l -> rev l = l.
Proof.
 intros l H; elim H; simpl; auto with datatypes.
 intros a l0 m H0 H1 H2.
 generalize H1; inversion_clear H2.
 simpl; auto.
 rewrite (remove_last_inv H3).
 simpl.
 repeat (rewrite rev_app; simpl).
 intro eg; rewrite eg.
 simpl; auto.
Qed.

(* A new induction principle for lists *)

(* preliminaries *)

Lemma length_app :
 forall l l':list A, length (l ++ l') = length l + length l'.
Proof.
  intro l; elim l; simpl; auto.
Qed.

Lemma fib_ind :
 forall P:nat -> Prop,
   P 0 ->
   P 1 -> 
  (forall n:nat, P n -> P (S n) -> P (S (S n))) -> 
  forall n:nat, P n.
Proof.
 intros P H0 H1 HSSn n.
 cut (P n /\ P (S n)).
 tauto. 
 elim n ;[tauto | idtac].
 destruct 1; split; auto.
Qed.


Lemma list_new_ind :
 forall P:list A -> Prop,
   P nil ->
   (forall a:A, P (a :: nil)) ->
   (forall (a b:A) (l:list A), P l -> P (a :: l ++ b :: nil)) ->
   forall l:list A, P l.
Proof.
 intros P H0 H1 H2.
 cut (forall (n:nat) (l:list A), length l = n -> P l).
 intros H l.
 eapply H.
 reflexivity.
 intro n; pattern n; apply fib_ind.
 intro l; case l; simpl; auto with datatypes.
 discriminate 1.
 intro l; case l; simpl.
 discriminate 1.
 intros a l0; case l0; simpl; auto.
 discriminate 1.
 intros n0 H3 H4 l.
 case l; simpl.
 discriminate 1.
 intros a l0 H5.
 generalize H5; case l0. 
 simpl; discriminate 1.
 intros a0 l1 H6.
 cut
  (forall (l:list A) (x:A),
      exists b : A, exists l' : list A, x :: l = l' ++ b :: nil).
 intros H.
 case (H l1 a0); intros x Hx.
 case Hx; intros x0 Hx0.
 rewrite Hx0.
 apply H2.
 apply H3.
 rewrite Hx0 in H6.
 rewrite length_app in H6.
 simpl in H6.
 Require Import Omega.
 omega.
 intro l2; elim l2; simpl.
 intro x; exists x; exists (nil (A:=A)); auto.
 intros a1 l3 H x.
 case (H a1).
 intros x0 H7.
 case H7; intros b Hb.
 rewrite Hb.
 exists x0.
 exists (x :: b); auto.
Qed. 


Lemma app_left_reg : forall l l1 l2:list A, l ++ l1 = l ++ l2 -> l1 = l2.
Proof.
 intro l; elim l; simpl; auto.
 intros a l0 H0 l1 l2 H; injection H; auto.
Qed.

Lemma app_right_reg : forall l l1 l2:list A, l1 ++ l = l2 ++ l -> l1 = l2.
Proof.
 intros l l1 l2 e.
 cut (rev (l1 ++ l) = rev (l2 ++ l)).
 repeat rewrite rev_app.
 intro H0; generalize (app_left_reg _ _ _ H0).
 intro H1; rewrite <- (rev_involutive l1); rewrite <- (rev_involutive l2).
 rewrite H1; auto.
 rewrite e; auto.
Qed.

Theorem rev_pal : forall l:list A, rev l = l -> palindromic l. 
Proof.
 intro l; elim l using list_new_ind; auto.
 intros a b l0 H H0.
 apply cons_pal with l0.
 apply H.
 simpl in H0.
 rewrite rev_app in H0.
 simpl in H0.
 injection H0.
 intros H1 e; generalize H1; rewrite e.
 intro H2.
 generalize (app_right_reg _ _ _ H2); auto.
 simpl in H0.
 rewrite rev_app in H0; simpl in H0.
 injection H0.
 intros H1 H2;elim H2.
 generalize l0.   
 intro l1; elim l1; simpl; auto.  
Qed.


End mirror.
