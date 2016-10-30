Require Import Arith.
Require Import Omega.

Fixpoint div2 (n:nat) : nat := match n with S (S p) => S (div2 p) | _ => 0 end.

(* as we advised in chapter 9, we use a specific induction principle
   to reason on the division function. *)

Theorem div2_ind :
 forall P:nat->Prop,
   P 0 -> P 1 -> (forall n, P n -> P (S (S n))) ->
   forall n, P n.
Proof.
 intros.
 assert (H' : P n /\ P (S n)).
 elim n; intuition.
 intuition.
Qed.

(* Once the induction principle breaks down the problem into the
   various cases, the omega tactic can handle them. *)

Theorem double_div2_le : forall x:nat, div2 x + div2 x <= x.
Proof.
 intros x; elim x using div2_ind; simpl; auto.
 intros; omega.
Qed.

(* Here we don't even need a proof by induction, but the previous
   theorem must be re-used. *)
Theorem f_lemma : forall x v, v <= div2 x -> div2 x + v <= x.
Proof.
 intros; generalize (double_div2_le x); omega.
Qed.

