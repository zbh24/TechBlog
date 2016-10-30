Require Import List.
Set Implicit Arguments.

Inductive lfactor (A:Set) : list A -> list A -> Prop :=
  | lf1 : forall u:list A, lfactor nil u
  | lf2 : forall (a:A) (u v:list A), lfactor u v ->
                                     lfactor (a :: u) (a :: v).

Definition lfactor_suffix :
  forall (A:Set) (u v:list A), lfactor u v -> {w : list A | v = u ++ w}.
 intros A u; elim u.
 intros v; exists v; auto.
 intros a u' Hrec v; case v.
 intros Hf; cut False.
 contradiction.
 inversion Hf.
 intros b v' Hf.
 elim (Hrec v').
 intros r Heq; exists r.
 inversion Hf.
 simpl in |- *; rewrite <- Heq.
 trivial.
 inversion Hf; assumption.
Defined.


  