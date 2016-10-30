Require Import Arith.
Require Import Morphisms.
Require Import Setoid.
Require Import Omega.

Instance plus_proper_le : Proper (le ==> le ==> le) plus.
intros x y Hxy  z t Hzt;omega. 
Qed.


Instance mult_proper_le : Proper (le ==> le ==> le) mult.
SearchAbout (_ * _ <= _ * _).
intros x y H z t H0;apply mult_le_compat;assumption.
Qed.

Goal forall a b c d e f:nat, a <= b -> c <= f -> a + c * e <= b +  f * e.
intros.
rewrite H, H0.
reflexivity.
Qed.


(* from Matthieu in Refman *)
Section Sets.
 Variable A : Type.

 Require Import List.
 
Notation set := (list A).
Definition subset (s s': set) := forall a, In a s -> In a s'.

Definition eqset (s s': set) := forall a, In a s <-> In a s'.


Infix "=s=" := eqset (at level 70). 
Infix "<s=" := subset (at level 70).

Instance subset_refl : Reflexive subset.
 red;unfold subset;auto.
Qed.

Instance subset_transitive : Transitive subset.
 red;unfold subset;auto.
Qed.

Instance eqset_refl : Equivalence eqset.
 split;red; red;unfold eqset;firstorder.
Qed.


Definition emptyset : set:= nil.

Definition union (s s':set) := s++s'.
Infix "+++" := union (at level 50, left associativity).

Global Instance union_subset : Proper (subset ==> subset ==> subset) union.
Proof.
 intros x y Hxy z t Hzt a Ina;unfold union.
SearchAbout (In _ (_ ++ _)).
rewrite in_app_iff in *.
firstorder.
Qed.


Global Instance eqset_subset : Proper (eqset ==> eqset ==> iff) subset.
intros x y Hxy  z t Hzt ;split;intros H a Ha;
 apply Hzt; apply Hxy in Ha;auto.  
Qed.


Global Instance subset_subset : Proper (subset --> subset ++> Basics.impl) subset.
intros x y Hxy  z t Hzt. red in Hxy; intros H a Ha;auto.
Qed.



Global Instance subset_subset_flip : Proper (subset ++> subset --> Basics.flip Basics.impl) subset.
intros x y Hxy  z t Hzt. red in Hxy; intros H a Ha;auto.
Qed.



Global Instance union_eqset : Proper (eqset ==> eqset ==> eqset) union.
Proof.
 intros x y Hxy z t Hzt a ;split; intro Ina;unfold union in *;
 rewrite in_app_iff in *; firstorder.
Qed.





Lemma union_comm : forall s s', s +++ s' =s= s' +++ s.
intros s s' a ;split;intro Ha; rewrite in_app_iff in *;firstorder.
Qed.

Lemma union_l : forall s s', s <s= s +++ s'.
Proof.
 intros s s' a Ha;unfold union in *;rewrite in_app_iff ; firstorder.
Qed.

Lemma union_r : forall s s', s' <s= s +++ s'.
Proof.
 intros s s' . 
 rewrite union_comm.  apply union_l.
Qed.


Lemma union_ass : forall s s' s'', s +++ s' +++ s'' =s= 
                                   s +++ (s' +++ s'').
Proof.
 intros s s' s'' a ;split;intro Ha; repeat rewrite in_app_iff in *;firstorder.
Qed.


Lemma union_idem : forall s, s +++ s =s= s.
Proof.
 intros s  a ;split;intro Ha; repeat rewrite in_app_iff in *;firstorder.
Qed.

Goal forall s s', s +++ s' +++ s =s= s +++ s'.
Proof.
 intros s s'; rewrite union_ass;rewrite union_comm at 1.
 rewrite  union_ass. rewrite union_idem. apply union_comm.
Qed.

End Sets.













