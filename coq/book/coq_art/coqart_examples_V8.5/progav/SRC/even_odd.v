Require Import Arith.

Definition Even (n:nat) : Prop :=
 exists p:nat, n = 2*p. 

Definition Odd (n:nat) : Prop :=
 exists p:nat, n = S (2*p).




Inductive even_spec (n:nat) : bool -> Prop :=
| even_true : forall (Heven : Even n), even_spec n true 
| even_false : forall (Hodd : Odd n), even_spec n false.


Definition even_test_ok (t : nat -> bool) :=
 forall n:nat, even_spec n (t n).


Fixpoint even_bool (n:nat) :=
 match n with 0 => true
           |  1 => false
           | S (S p)=> even_bool p
end.


 Lemma Even_not_Odd : forall n, Even n -> ~ Odd n. 
 Proof.
  intros n [p Hp] [q Hq].
  rewrite Hp in Hq.
 Require Import Omega.
 omega.
 Qed.


Lemma nat_double_ind : forall (P:nat->Prop),
     P 0 -> P 1 -> (forall p, P p -> P (S (S p))) ->
    forall n:nat, P n.
Proof.
 intros P H0 H1 HS.
 assert (forall n, P n /\ P (S n)).
 induction n.
 split;auto.
 destruct IHn;auto.
 intro n;destruct (H n);auto.
Qed.
   
Lemma even_spec_SS : forall n b, even_spec n b -> even_spec (S (S n)) b.
destruct 1.

destruct Heven as [q Hq];constructor;exists (S q);omega.
destruct Hodd as [q Hq]. constructor ;exists (S q);omega.
Qed.

Lemma even_bool_correct : even_test_ok  even_bool. 
Proof.
 intro n;induction n using nat_double_ind.
 constructor;exists 0;trivial.
  constructor;exists 0;trivial.

simpl;apply even_spec_SS;assumption. 
Qed.

Section use_of_even_bool_correct.

Variable P : nat -> bool -> Prop.

Goal forall n, P n (even_bool n).
Proof.
  intros n ;destruct (even_bool_correct n).
(* 
2 subgoals
  
  P : nat -> bool -> Prop
  n : nat
  Heven : Even n
  ============================
   P n true

subgoal 2 is:

 P : nat -> bool -> Prop
  n : nat
  Hodd : Odd n
  ============================
   P n false
*)
Abort.

End use_of_even_bool_correct.



Lemma even_bool_false : forall n,  Odd n <-> even_bool n = false.
intros n ;destruct (even_bool_correct n).

(* subgoals
  
  n : nat
  Heven : Even n
  ============================
   Odd n <-> true = false *)

split;try discriminate;intro;destruct (Even_not_Odd n);auto.
(*
1 subgoal
  
  n : nat
  Hodd : Odd n
  ============================
   Odd n <-> false = false
*)

tauto.
Qed.





