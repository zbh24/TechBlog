Require Export Arith.
Require Export ZArithRing.
Require Export Omega.

Theorem Frobenius_3_8 :
  forall n:nat,
    8 <= n -> (exists p:nat, (exists q:nat, n = 3 * p + 5 * q)).
Proof.
 intros n Hle; elim Hle.
 exists 1; exists 1; ring.
 intros n' Hle' [p' [q']].
 case q'.
 intros Heq.
 assert (H3lep': 3 <= p').
 omega.
 exists (p' - 3); exists 2.
 rewrite Heq.
 replace (3*(p'-3)+5*2) with (S (3*3+3*(p'-3))).
 rewrite <- mult_plus_distr_l.
 rewrite le_plus_minus_r; auto.
 ring.
 intros q'' Heq; exists (p'+2); exists q''; rewrite Heq.
 ring.
Qed.
