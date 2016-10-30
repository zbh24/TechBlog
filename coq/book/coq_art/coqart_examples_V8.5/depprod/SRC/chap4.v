
Require Export ZArith.
Require Export List.
Require Export Arith.
Require Export ZArithRing.
Require Arith.

Parameters (prime_divisor : nat->nat)
           (prime : nat->Prop)
           (divides : nat->nat->Prop).

Check (prime (prime_divisor 220)).

Check (divides (prime_divisor 220) 220).

Check (divides 3).

Parameter binary_word : nat->Set.

Definition short : Set := binary_word 32.
Definition long : Set := binary_word 64.

Check (~ divides 3 81).

Check (let d := prime_divisor 220 in prime d /\ divides d 220).

Parameters (decomp : nat -> list nat)
           (decomp2 : nat->nat*nat).

Check (decomp 220).

Check (decomp2 284).

Check(forall n:nat, 2<=n ->
       prime (prime_divisor n) /\ divides (prime_divisor n) n).

Parameter
  prime_divisor_correct :
     forall n:nat, 2 <= n -> 
       let d := prime_divisor n in prime d /\ divides d n.
Parameter
  binary_word_concat :
     forall n p:nat,
       binary_word n -> binary_word p -> binary_word (n+p).

Check cons.

Check pair.

Check (forall A B :Set, A->B->A*B).

Check fst.

Check le_n.

Check le_S.

Check (le_n 36).

Definition le_36_37 := le_S 36 36 (le_n 36).

Check le_36_37.

Definition le_36_38 := le_S 36 37 le_36_37.

Check le_36_38.

Check (le_S _ _ (le_S _ _ (le_n 36))).

Check (prime_divisor_correct 220).

Fixpoint iterate (A:Set)(f:A->A)(n:nat)(x:A){struct n} : A :=
  match n with
  | O => x
  | S p => f (iterate A f p x)
  end.

Check (iterate nat).


Check (iterate _ (mult 2)).

Check (iterate _ (mult 2) 10).

Check (iterate _ (mult 2) 10 1).

Eval compute in (iterate _ (mult 2) 10 1).

Check (binary_word_concat 32).

Check (binary_word_concat 32 32).

Definition binary_word_duplicate (n:nat)(w:binary_word n) 
 : binary_word (n+n) :=
  binary_word_concat _ _ w w.

Theorem le_i_SSi : forall i:nat, i <= S (S i).
Proof (fun i:nat => le_S _ _ (le_S _ _ (le_n i))).

Definition compose : forall A B C : Set, (A->B)->(B->C)->A->C
   := fun A B C f g x => g (f x).

Print compose.

Check (fun (A:Set)(f:Z->A) => compose _ _ _ Z_of_nat f).

Check (compose _ _ _ Zabs_nat (plus 78) 45%Z).

Check (le_i_SSi 1515).

Check (le_S _ _ (le_i_SSi 1515)).

Implicit Arguments compose [A B C].
Implicit Arguments le_S [n m].

Check (compose Zabs_nat (plus 78)).

Check (le_S (le_i_SSi 1515)).

Check (compose (C := Z) S).

Check (le_S (n := 45)).

Reset compose.
Set Implicit Arguments.

Definition compose (A B C:Set)(f:A->B)(g:B->C)(a:A) := g (f a).

Definition thrice (A:Set)(f:A->A) := compose f (compose f f).

Unset Implicit Arguments.

Print compose.

Print thrice.

Eval cbv beta delta in (thrice (thrice (A:=nat)) S 0).

Definition short_concat : short->short->long 
                        := binary_word_concat 32 32.

Check (forall i:nat, i <= S (S i)).

Check (forall n p:nat, 
         binary_word n -> binary_word p -> binary_word (n+p)
       ).

Check (forall n:nat, 0 < n -> nat).

Check iterate.

Definition my_plus : nat->nat->nat := iterate nat S.

Definition my_mult (n p:nat) : nat := iterate nat (my_plus n) p 0.

Definition my_expo (x n:nat) : nat := iterate nat (my_mult x) n 1.

Definition ackermann (n:nat) : nat->nat :=
  iterate (nat->nat)
          (fun (f:nat->nat)(p:nat) => iterate nat f (S p) 1) 
          n
          S.

Check (forall P:Prop, P->P).

Check (fun (P:Prop)(p:P) => p).

Check refl_equal.

Theorem ThirtySix : 9*4=6*6.
Proof (refl_equal 36).

Definition eq_sym  (A:Type)(x y:A)(h : x=y) : y=x :=
 eq_ind  x (fun z => z=x) (refl_equal x) y h.

Check (eq_sym _ _ _ ThirtySix). 

Check conj.

Check or_introl.

Check or_intror.

Check and_ind.

Theorem conj3 : forall P Q R:Prop, P->Q->R->P/\Q/\R.
Proof (fun P Q R p q r => conj p (conj q r)).

Theorem disj4_3 : forall P Q R S:Prop, R -> P\/Q\/R\/S.
Proof 
 (fun P Q R S r => or_intror _ (or_intror _ (or_introl _ r))).

Definition proj1' :  forall A B:Prop, A/\B->A :=
 fun (A B:Prop)(H:A/\B) => and_ind (fun (H0:A)(_:B) => H0) H.

Check (ex (fun z:Z => (z*z <= 37 /\ 37 < (z+1)*(z+1))%Z)).

Check ex_intro.

Check ex_ind.

Check and.
