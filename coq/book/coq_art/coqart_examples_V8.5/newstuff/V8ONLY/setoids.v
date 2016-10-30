(* Setoids for Beginners / Setoides pour les Nuls *)
(**************************************************)

(* Pierre Castéran *)


Require Import Setoid.
Require Import Arith.
Require Import Relations.
Require Import Compare_dec.
Require Import ArithRing. 
Require Import Omega.
Set Implicit Arguments.


(* We represent integers as pairs of Peano numbers *)

Delimit Scope Z'_scope with Z'.

Open Scope Z'_scope.


Inductive Z' : Set :=
 mkZ' : nat -> nat -> Z'.


(* The equivalence relation on Z' *)

Definition  Z'eq (z z':Z') :  Prop :=
 let (a, b) := z in
   let (c, d) := z' in  a + d = b + c.

Notation "a =Z= b" := (Z'eq a b)  (at level 70): Z'_scope.


(* a characteristic property of =Z= *)

Lemma Z'eq_inv : forall a b c d, mkZ' a b =Z= mkZ' c d ->
                       {q:nat | (a = q + b /\ c = q + d) \/
                                (b = q + a /\ d = q + c)}.
Proof.
 intros a b c d H ; simpl in H.
 case (le_lt_dec a b).
 exists (b-a); right; omega.
 exists (a-b); left; omega.
Qed.


(* Z'eq is an equivalence relation *)

Lemma Z'eq_refl : reflexive Z' Z'eq. 
Proof.
  unfold reflexive.
  intro z; case z.
  unfold Z'eq.
  auto with arith.
Qed.


Lemma Z'eq_sym : symmetric _ Z'eq.
Proof.
  unfold symmetric.
  intros z z'; case z; case z'.
  intros a b c d H.
  unfold Z'eq.
  symmetry.
  simpl in  H.
  rewrite (plus_comm b c). 
  rewrite (plus_comm a d). 
  trivial.
Qed.

Lemma Z'eq_trans : transitive _ Z'eq.
Proof.
 unfold transitive.
 intros x y z; case x;case y;case z.
 unfold Z'eq;intros;omega.
Qed.

(* We can now build a setoid *)

Theorem Z'oid : Setoid_Theory _ Z'eq.
 split.
 exact Z'eq_refl.
 exact Z'eq_sym.
 exact Z'eq_trans.
Qed.

Add Setoid Z' Z'eq Z'oid as Z'_setoid.

(* definition of operations in Z' *)


Definition Z'_plus (z z':Z') :=
 let (a, b) := z in
   let (c, d) := z' in  mkZ'( a + c)(b + d).

Notation "z + z'" := (Z'_plus z z'): Z'_scope.

Add Morphism Z'_plus : Z'_plus_morph.
 intros x y Hxy x0 y0 Hxy0;
   destruct x ; destruct y; destruct x0; destruct y0.
   simpl in *; omega. 
Qed.


Definition Z'_mult (z z':Z') :=
 let (a, b) := z in
   let (c, d) := z' in  mkZ'( a*c + b*d)(a*d + b*c).

Notation "z * z'" := (Z'_mult z z'): Z'_scope.

Add Morphism Z'_mult : Z'_mult_morph.
 intros x y Hxy x0 y0 Hxy0;
   destruct x ; destruct y; destruct x0; destruct y0.
   simpl in *. 
 case (Z'eq_inv  Hxy).
 case (Z'eq_inv  Hxy0).
 destruct 1; destruct 1.
 case H;case H0; intros; subst n1; subst n;subst n5; subst n3.
 clear Hxy H0 Hxy0 H;simpl.
 ring.
case H;case H0; intros; subst n3; subst n5;subst n2; subst n0.
 clear Hxy H0 Hxy0 H;simpl.
 ring.

 case H;case H0; intros; subst n1;subst n; subst n6;subst n4.
 clear H0 H Hxy Hxy0;simpl.
 ring.
 case H;case H0; intros; subst n2;subst n0; subst n6;subst n4.
clear H0 H Hxy Hxy0;simpl.
 ring.
Qed.

Definition Z'_opp (z:Z') := let (a,b) := z in (mkZ' b a).

Add Morphism Z'_opp : Z'_opp_morph .
Proof.
 intros z z'; case z;case z'.
 intros a b a' b' e; case (Z'eq_inv  e).
 intros x [(Ha',Ha)|(Hb',Hb)].
 subst a;subst a'; simpl; auto with arith.
 subst b; subst b';simpl;auto with arith.
Qed.


Definition Z'_zero := mkZ' 0 0.

Definition Z'_one := mkZ' 1 0.

Theorem Z'_zero_l : forall z, Z'_zero + z =Z=  z.
Proof.
 intro z; case z; simpl.
 auto with arith.
Qed.

Theorem Z'_zero_r : forall z, z + Z'_zero =Z=  z. 
Proof.
 intro z; case z; simpl.
 intros; omega.
Qed.

Theorem Z'_plus_assoc : forall z z' z'', z + (z' + z'') =Z= (z + z') + z''.
Proof.
 destruct z; destruct z'; destruct z''.
 simpl.
 ring.
Qed.

Theorem Z'_mult_assoc : forall z z' z'', z * (z' * z'') =Z= (z * z') * z''.
Proof.
 destruct z; destruct z'; destruct z''.
 simpl.
 ring.
Qed.


Theorem Z'_1_l : forall z, Z'_one * z =Z= z.
Proof.
 destruct z;simpl.
 ring.
Qed.


Theorem Z'_1_r : forall z, z =Z= Z'_one * z.
Proof.
 destruct z;simpl.
 ring.
Qed.

Theorem Z'_plus_comm : forall z z', z + z' =Z= z' + z.
Proof.
 destruct z; destruct z';simpl.
 ring.
Qed.

Theorem Z'_mult_comm : forall z z', z * z' =Z= z' * z.
Proof.
 destruct z; destruct z';simpl.
 ring.
Qed.


Theorem Z'_mult_dist : forall z z' z'', (z + z') * z'' =Z= z * z'' + z' * z''.
Proof.
 destruct z;destruct z';destruct z''.
 simpl.
 ring.
Qed.

(* technical lemma for proving integrity *)

Lemma diff : forall a b:nat , {d:nat | (a = b + d \/ b = a + d)%nat}.
Proof.
 intros a b; case (le_lt_dec a b).
 exists (b-a); right ;  omega.
 exists (a-b);left;omega.
Qed.

Lemma nat_mult_is_zero : forall x y:nat, mult x y = 0 -> x = 0 \/ y = 0. 
Proof.
 destruct x; destruct y;auto.
 simpl; discriminate 1.
Qed.


Theorem Z'_integrity : forall z z', z * z' =Z= Z'_zero -> 
                                    z =Z= Z'_zero \/
                                    z' =Z= Z'_zero.
Proof.
 intros z z' ; case z ; case z'; simpl; intros a b c d H.

 case (diff a b); case (diff c d).

 intros x [Hx|Hx] y [Hy|Hy];
 [ (subst a; subst c) | 
   (subst c; subst b) | 
   (subst d; subst a) | 
   (subst d;subst b)];
 (do 2 rewrite plus_0_r in H;
 repeat rewrite mult_plus_distr_l in H;
 repeat rewrite mult_plus_distr_r in H;
 repeat rewrite plus_assoc in H;
 assert (x*y=0)%nat;[ omega | idtac];
 case (nat_mult_is_zero _ _ H0);[
 intro;subst x;left;auto with arith |
 intro;subst y;right;auto with arith]).
Qed.


Lemma plenty_of_zeros : forall n, Z'eq (mkZ' n n) (mkZ' 0 0).
Proof.
  simpl.
  auto with arith.
Qed.

Lemma plenty_of_neutral : forall n z, Z'eq (Z'_plus (mkZ' n n) z) z.
Proof.
  intros.
  setoid_rewrite (plenty_of_zeros n).
  (*
  !!!!!!!!

  setoid_rewrite (Z'_zero_l z) 

   doesn't work !
  
  *)
  generalize (Z'_zero_l z).
  intro H.
  unfold Z'_zero in H. 
  setoid_rewrite H.

  apply Z'eq_refl.
Qed.



Definition Z'_sub (z z':Z') := z + (Z'_opp z').

Notation "z - z'" := (Z'_sub z z'): Z'_scope.

Add Morphism Z'_sub : Z'_sub_morph.
 unfold Z'_sub.
 intros z z0 e z1 z2  e'.
 setoid_rewrite e.
 setoid_rewrite e'.
 apply Z'eq_refl.
Qed.



(* Building Z modulo p *)
(***********************)

(* multiplication  : nat -> Z' -> Z' *)

Definition external_mult (n:nat)(z:Z') : Z' :=
let (a,b) := z
in mkZ' (mult n a) ( mult n b).


Add Morphism external_mult : external_morph.
 intros n z z0;case z; case z0.
 simpl.
 intros.
 transitivity (n*(n2+n1))%nat.
 ring.
 transitivity (n*(n3+n0))%nat.
 rewrite H;trivial.
 ring.
Qed.


Lemma external_zero : forall p, external_mult p (Z'_zero) =Z= Z'_zero.
Proof.
 induction p.
 simpl.
 auto.
 unfold Z'_zero.
 simpl; auto.
Qed.


(* equivalence modulo p *)

Inductive Z'_mod (p:nat)(z z':Z'):Prop :=
Z'_mod_i:  forall q, z - z' =Z= external_mult p q -> Z'_mod p z z'.

Lemma mod_refl : forall p z, Z'_mod p z z.
Proof.
  destruct z;simpl.
  exists (Z'_zero).
 simpl.
 auto with arith.
Qed.

Lemma mod_sym : forall p z z', Z'_mod p z z' -> Z'_mod p z' z.
Proof.
 destruct z;destruct z'.
 inversion 1.
 exists (Z'_opp q).
 simpl.
 simpl in H0.
 generalize q H0.
 clear H0. destruct q0.
 simpl.
 intro.
 omega.
Qed.

Lemma mod_trans : forall p z z' z'', Z'_mod p z z' -> Z'_mod p z' z'' ->
                                     Z'_mod p z z'' .
Proof.
 destruct z;destruct z'; destruct z''.
 inversion 1.
 inversion 1.
 exists (q+q0).
 generalize q H0 q0 H2.
 destruct q1.
 destruct q1.
 simpl.
 simpl in H3.
 intro.
 repeat rewrite mult_plus_distr_l.
 omega.
Qed.


Lemma mod_plus_compat_l  : forall p z z0 z1,
                           Z'_mod p z0 z1 -> 
                           Z'_mod p (z+z0) (z+z1).
Proof.
 destruct z.
 destruct z0.
 destruct z1.
 inversion 1.
 exists q.
 generalize H0;case q.
 simpl.
 intros.
 omega.
Qed.

Lemma mod_plus_compat_r  : forall p z z0 z1,
                           Z'_mod p z0 z1 -> 
                           Z'_mod p (z0+z) (z1+z).
Proof.
 destruct z.
 destruct z0.
 destruct z1.
 inversion 1.
 exists q.
 generalize H0;case q.
 simpl.
 intros.
 omega.
Qed.

Lemma mod_plus_compat : forall p z z0 z1 z2, 
 Z'_mod p z z0 -> Z'_mod p z1 z2 ->  Z'_mod p (z+z1) (z0+z2).
Proof.
 intros.
 apply mod_trans with (z0+z1).
 apply mod_plus_compat_r; trivial.
 apply mod_plus_compat_l;trivial.
Qed.


(* let's build a new type upon Z' *)

Inductive Zmod : Set := zmod : Z' -> Zmod.

Definition modeq (p:nat)(m m':Zmod) :=
   let  (z) := m in
    let (z') := m' in
     Z'_mod p z z'.

Definition zmodplus (p:nat)(m m':Zmod) :=
   let  (z) := m in
    let (z') := m' in
      zmod  (z + z').

Lemma ZMT : forall p, Setoid_Theory Zmod  (modeq p).
Proof.
 split.
 intro x;destruct x.
 
 apply mod_refl.
 intros x y;destruct x;destruct y;simpl;apply mod_sym.
 intros x y z; case x;case y;case z; simpl; intros.
 eapply mod_trans;eauto.
Qed.


(* Since setoid_rewrite requires non dependent products, we have to fix
   now the value of p *)

Definition eq16 := modeq 16.
Add Setoid Zmod eq16 (ZMT 16) as S16.

Definition plus16 := zmodplus 16.

Notation "a =16= b" := (eq16 a b) (at level 70): mod16_scope.
Notation "a + b" := (plus16 a b) :mod16_scope.
Notation "'cl' a" := (zmod (mkZ' a 0)) (at level 29) :mod16_scope.
Open Scope mod16_scope.

 
Add Morphism plus16 : plus16_morph.
Proof.
 intros z z0 H z1 z2 H0;destruct z;destruct z0; destruct z1; destruct z2;simpl.
 intros;apply mod_plus_compat;auto.
Qed.


Lemma cl_morph : forall n p:nat ,cl (n+p) =16= cl n + cl p.
Proof. 
 simpl.
 intros; apply mod_refl.
Qed.


Goal (cl 13) + (cl 13) =16= (cl 10).
 setoid_rewrite <- (cl_morph 13 13).  
 simpl.
 exists (mkZ' 1 0).
 simpl;auto.
Qed.










  
  
