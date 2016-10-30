Require Import List.
Section Last.

Variable A : Set.
Set Implicit Arguments.

Inductive last (a:A) : list A -> Prop :=
   | last_hd : last a (a :: nil)
   | last_tl : forall (b:A) (l:list A), last a l -> last a (b :: l).


Hint Resolve last_hd last_tl.

Fixpoint last_fun (l:list A) : option A :=
  match l with
  | nil => None (A:=A)
  | a :: nil => Some a
  | a :: l' => last_fun l'
  end.

Theorem last_fun_correct :
 forall (a:A) (l:list A), last a l -> last_fun l = Some a.
Proof.
 intros a l H; elim H; simpl; auto.
 intros b l0; case l0; simpl.
 discriminate 2.
 inversion_clear 1; auto.
Qed.

Theorem last_fun_correct2 :
 forall (a:A) (l:list A), last_fun l = Some a -> last a l.
Proof.
 intros a l ; elim l; simpl.
 discriminate 1.
 intros a0 l0; case l0; simpl.
 injection 2.
 intro e; rewrite e; auto.
 auto.
Qed.

Lemma last_fun_of_cons : forall (l:list A) (a:A), last_fun (a :: l) <> None.
Proof.
 intros l ; elim l; simpl.
 intros a H; discriminate H.
 intros a l0 H0 b.
 auto.
Qed.

Theorem last_fun_correct3 :
 forall l:list A, last_fun l = None -> forall b:A, ~ last b l.
Proof.
 intro l; case l.
 simpl.
 red; inversion 2.
 intros a l0 H. 
 case (last_fun_of_cons l0 a H). 
Qed.

End Last.
