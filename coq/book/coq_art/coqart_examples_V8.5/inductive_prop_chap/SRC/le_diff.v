Inductive le_diff (n m:nat) : Prop :=
    le_d : forall x:nat, x + n = m -> le_diff n m.


Definition le_diff' (n m:nat) :=  exists x : _, x + n = m.


Theorem le_le_diff : forall n m:nat, n <= m -> le_diff n m.
Proof.
 intros n m l; elim l; clear l m.
 exists 0; reflexivity.
 intros m l [x Hx].
 rewrite <- Hx; exists (S x); reflexivity.
Qed.

Theorem le_diff_le : forall n m:nat, le_diff n m -> n <= m.
Proof.
 intros n m l; case l; clear l; intro x.
 generalize m; clear m. 
 elim x; clear x. 
 intros m e; case e; constructor.
 intros x Hrec m e. 
 case e; simpl; constructor 2.
 apply Hrec; reflexivity.
Qed.

Theorem le_le_diff' : forall n m:nat, n <= m -> le_diff' n m.
Proof.
 intros n m l; elim l; clear l m.
 exists 0; reflexivity.
 intros m l [x Hx].
 rewrite <- Hx; exists (S x); reflexivity.
Qed.

Theorem le_diff'_le : forall n m:nat, le_diff' n m -> n <= m.
Proof.
 intros n m l; case l; clear l; intro x.
 generalize m; clear m. 
 elim x; clear x. 
 intros m e; case e; constructor.
 intros x Hrec m e. 
 case e; simpl; constructor 2.
 apply Hrec; reflexivity.
Qed.

