Require Import Arith.
Require Import Compare_dec.

Definition max (n p:nat) : nat :=
  if le_lt_dec n p then p else n.

Lemma le_max_eq :  forall n p, n <= p -> p = max n p.
 intros n p; unfold max; case (le_lt_dec n p);simpl.
 trivial.
 intros; apply le_antisym;auto with arith.
Qed.

Ltac max_le_rw H :=
 match goal with H : ?a <= ?b |- ?G =>  elim (le_max_eq a b H) end.

Lemma L1: forall n p, n <= p -> max n p + max n p = 2 * p.
 intros n p H; max_le_rw H.
 simpl;auto.
Qed.

Lemma L2 :  forall n p, n <= p -> 2 <= 3 -> max n p + max n p = 2 * p.
 intros n p H H0. 
 max_le_rw H.
 (* 
  n : nat
  p : nat
  H : n <= p
  H0 : 2 <= 3
  ============================
   max n p + max n p = 2 * p
*)


Ltac max_le_rw' H :=
  let typ := type of H in
    match typ with ?a <= ?b   => elim  (le_max_eq a b H) end.

 (* works now ! *)

 max_le_rw' H.
 simpl;auto.
Qed.


