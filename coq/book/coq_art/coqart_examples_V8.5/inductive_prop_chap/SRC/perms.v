Require Import List.

Set Implicit Arguments.

Require Import Relations.
Section perms.
Variable A : Set.

 Inductive transpose : list A -> list A -> Prop :=
   | transpose_hd :
       forall (a b:A) (l:list A), transpose (a :: b :: l) (b :: a :: l)
   | transpose_tl :
       forall (a:A) (l l':list A),
         transpose l l' -> transpose (a :: l) (a :: l').


Inductive perm (l:list A) : list A -> Prop :=
  | perm_id : perm l l
  | perm_tr :
      forall l' l'':list A, perm l l' -> transpose l' l'' -> perm l l''.


Lemma perm_refl : reflexive _ perm. 
Proof.
  unfold reflexive; left.
Qed.


Lemma perm_intro_r :
 forall l l1 l2:list A, transpose l l1 -> perm l1 l2 -> perm l l2.
Proof.
 intros l l1 l2 H H0; elim H0.
 eapply perm_tr; eauto.
 left.
 intros l' l''; intros; right with l'; auto.
Qed.

Lemma perm_trans : transitive _ perm.
Proof.
 unfold transitive; intros l l' l'' H; generalize l''.
 elim H.
 trivial.
 intros l'0 l''0 H0 H1; intros.
  apply H1;eapply perm_intro_r; eauto.
Qed.

Lemma transpose_sym : forall l l':list A, transpose l l' -> transpose l' l.
Proof.
 intros l l' H;elim H; [ left | right; auto ].
Qed.

Lemma perm_sym : symmetric _ perm. 
Proof.
 unfold symmetric; intros l l' H; elim H. 
 left.
 intros; eapply perm_intro_r.
 eapply transpose_sym; eauto.
 auto.
Qed.


Theorem equiv_perm : equiv _ perm.
Proof.
 repeat split.
 apply perm_refl.
 apply perm_trans.
 apply perm_sym.
Qed.


End perms.
