Require Import Ring.
 Locate  semi_ring_theory.

 Variable A : Type.
  Variables zero one : A.
  Variables plus mult : A -> A -> A.
  About semi_ring_theory.
  Variable srt : semi_ring_theory  zero one plus mult (@eq A).

 
 Add  Ring Aring :  srt.

Print semi_ring_theory.
Goal plus zero one = one.
ring.
Qed.

