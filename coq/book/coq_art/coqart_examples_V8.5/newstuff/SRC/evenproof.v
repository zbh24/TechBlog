Require Import Arith.

Fixpoint exp2 (n:nat) : nat :=
  match n with 0 => 1
             | S p => 2 * (exp2 p)
  end.

Fixpoint tower2 (n:nat) : nat :=
  match n with 0 => 1
             | S p => exp2 (tower2 p)
  end.

Eval compute in (tower2 3).


Inductive even : nat -> Prop :=
  even0 : even 0
| even_S : forall p, even p -> even (S (S p)).

Hint Constructors even.


Theorem even_double : forall n, even (2*n).
 induction n. 
 simpl;auto.
 simpl in IHn; simpl.
 rewrite <- plus_n_Sm.
 auto.
Defined.
Hint Resolve even_double.

Theorem even_exp2 : forall n, 0 < n -> even (exp2 n).
 intro n; case n.
 inversion 1.
 intros; change (even (2 * (exp2 n0))).
 auto.
Defined.


Theorem exp2_positive : forall n, 0 < exp2 n.
Proof.
 induction n.
 simpl;auto.
 simpl.
 Require Import Omega.
 omega.
Defined.


 
Theorem even_tower2 : forall n, 0 < n -> even (tower2 n).
Proof.
 intro n; case n.
 inversion 1.
 simpl.
 intros;apply even_exp2.
 case n0;simpl;auto.
 intros;apply exp2_positive.
Defined.

Lemma four_tower : even (tower2 4).
 apply even_tower2.
 auto with arith.
Defined.


Lemma three_tower : even (tower2 3).
 apply even_tower2.
 auto with arith.
Defined.

Eval compute in three_tower.

Lemma six_tower : even (tower2 6).
 apply even_tower2.
 auto with arith.
Defined.

 
 
