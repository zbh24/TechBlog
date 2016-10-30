Require Import Arith.

Record RatPlus : Set := mkRat
  {top : nat; bottom : nat; bottom_condition : bottom <> 0}.

Axiom
  eq_RatPlus :
    forall r r':RatPlus, top r * bottom r' = top r' * bottom r -> r = r'.


Definition r0 : RatPlus.
Check mkRat.
 apply (mkRat 4 6).
 (* variant : Refine (mkRat (4) (6) ?)  *)
 auto with arith.
Defined.

Definition r1 : RatPlus.
 apply (mkRat 2 3); auto with arith.
Defined.

Lemma r0_eq_r1 : r0 = r1.
Proof.
 apply eq_RatPlus; auto.
Qed.

Lemma r0_diff_r1 : r0 <> r1.
Proof.
 unfold not; intro H; discriminate H.
Qed.

Lemma contrad : False.
Proof.
 elim (r0_diff_r1 r0_eq_r1).
Qed.

