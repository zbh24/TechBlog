Require Import Arith.

Lemma fib_ind :
 forall P:nat -> Prop,
   P 0 ->
   P 1 -> 
  (forall n:nat, P n -> P (S n) -> P (S (S n))) -> 
  forall n:nat, P n.
Proof.
 intros P H0 H1 HSSn n.
 cut (P n /\ P (S n)).
 tauto.
 elim n.
 split; auto.
 intros n0 Hn0; case Hn0; auto.
Qed.


Fixpoint fib (n:nat) : nat :=
  match n with
  | O => 1
  | S O => 1
  | S (S p as q) => fib p + fib q
  end.

(* A geralisation of the fibonacci sequence, parameterized by
   its two first items *)

Fixpoint general_fib (a0 a1 n:nat) {struct n} : nat :=
  match n with
  | O => a0
  | S p => general_fib a1 (a0 + a1) p
  end.

Definition fib_tail (n:nat) := general_fib 1 1 n.

Eval compute in (fib_tail 10).


Lemma general_fib_1 : forall a b:nat, general_fib a b 1 = b.
Proof.
 simpl; auto.
Qed.

Lemma general_fib_S :
 forall a b n:nat, general_fib a b (S n) = general_fib b (a + b) n.
Proof.
 simpl; auto.
Qed.

Lemma general_fib_2 :
 forall a b n:nat,
   general_fib a b (S (S n)) = general_fib a b n + general_fib a b (S n).
Proof.
 intros a b n; generalize a b.
 elim n.
 simpl; auto.
 intros n0 H a0 b0.
 pattern (general_fib a0 b0 (S (S (S n0)))); rewrite general_fib_S.
 pattern (general_fib a0 b0 (S (S n0))); rewrite general_fib_S.
 pattern (general_fib a0 b0 (S n0)); rewrite general_fib_S.
 apply H.
Qed.

Lemma fib_SSn : forall n:nat, fib (S (S n)) = fib n + fib (S n).
Proof.
 simpl; auto.
Qed.

Lemma linear_fibo_equiv : forall n:nat, fib_tail n = fib n.
Proof.
 intro n; elim n using fib_ind.  
 simpl; auto. 
 simpl; auto. 
 unfold fib_tail.
 intros n0 e0 e1; rewrite general_fib_2. 
 rewrite e0; rewrite e1.
 rewrite fib_SSn; trivial.
Qed.




