Require Import Arith.
Require Import Omega.

(* Let us consider our old friends Even and Odd, with very naïve
  definitions *)

Definition Even (n:nat) : Prop :=
 exists p:nat, n = 2*p. 

Definition Odd (n:nat) : Prop :=
 exists p:nat, n = S (2*p).

Lemma Even_not_Odd : forall n, Even n -> not (Odd n).
Proof.
  intros n [p Hp] [q Hq];rewrite Hq in Hp;omega.
Qed.
 
(* we specify how a boolean can reflect the evenness of n *)
Inductive even_spec (n:nat) : bool -> Prop :=
| even_true : forall (Heven : Even n), even_spec n true 
| even_false : forall (Hodd : Odd n), even_spec n false.

Check even_spec_ind.

(*

even_spec_ind
     : forall (n : nat) (P : bool -> Prop),
       (Even n -> P true) ->
       (Odd n -> P false) -> forall b : bool, even_spec n b -> P b

*)



Goal even_spec 42 true.
constructor;exists 21;trivial.
Qed.

Goal even_spec 23 false.
constructor;exists 11;trivial.
Qed.



Definition even_OK (f:nat->bool) :=
  forall n, even_spec n (f n).

(* let us consider a boolean funtion *)

Fixpoint even_test (n:nat) : bool :=
 match n with 0 => true
            | 1 => false
            | S (S p) => even_test p
 end.

(* already in the std lib or elsewhere in the book ? *)

Lemma nat_double_induction : 
  forall (P:nat->Prop),
    P 0 ->P 1 -> (forall p, P p -> P (S (S p))) ->
   forall n:nat, P n.
Proof.
  intros P H0 H1 H_ind.
  assert (H2:forall n, P n /\ P (S n)).
  induction n.
  split;auto.
  destruct IHn;split;auto.
  firstorder.
Qed.




Lemma even_correct : even_OK even_test.
Proof. 
 intro n;induction n using nat_double_induction.
 simpl;constructor;exists 0;trivial.
  simpl;constructor;exists 0;trivial.
 simpl.
destruct IHn.
constructor.
destruct Heven as [p Hp];exists (S p);subst n;ring.
constructor;
destruct Hodd as [p Hp] ;exists (S p);subst n;ring.
Qed.

Goal forall n, Even n <-> even_test n = true.
intro n. case (even_correct n).
(*
2 subgoals
  
  n : nat
  Heven : Even n
  ============================
   Even n <-> true = true


 subgoal 2 :
  
  n : nat
  Hodd : Odd n
  ============================
   Even n <-> false = true



*)

tauto.
split;[intro H;destruct (Even_not_Odd _ H);assumption|discriminate].
Qed.


(*** Specification of a comparison fonction *)


Inductive CompSpec {A} (eq lt : A->A->Prop)(x y:A) : comparison -> Prop :=
 | CompEq : forall (H_eq:eq x y), CompSpec eq lt x y Eq
 | CompLt : forall (H_lt:lt x y), CompSpec eq lt x y Lt
 | CompGt : forall (H_gt: lt y x), CompSpec eq lt x y Gt.



Fixpoint cmp (n p :nat) : comparison :=
  match n, p with 0, 0 => Eq
                | 0, S _ => Lt
                | S _, 0 => Gt
                | S q, S r => cmp q r
  end.

Lemma cm_correct : forall n p, CompSpec eq lt n p (cmp n p).
Proof.
 induction n;destruct p;simpl;try constructor;auto with arith.
 destruct (IHn p).
 subst p;constructor;trivial.
 constructor;auto with arith.
 constructor;auto with arith.
Qed.

Lemma cmp_nn : forall n, cmp n n = Eq.
Proof.
 induction n;simpl;auto.
Qed.

 
Lemma cmp_sym : forall n p , cmp n p = Gt <-> cmp p n = Lt.


intros  n p;destruct (cm_correct n p);destruct (cm_correct p n).
(*

  
  n : nat
  p : nat
  H_eq : n = p
  H_eq0 : p = n
  ============================
   Eq = Gt <-> Eq = Lt

Subgoal 2 is:

  n : nat
  p : nat
  H_eq : n = p
  H_lt0 : p < n
  ============================
   Eq = Gt <-> Lt = L

...

subgoal 9 is:
  
  n : nat
  p : nat
  H_gt : p < n
  H_gt0 : n < p
  ============================
   Gt = Gt <-> Gt = Lt

*)

Restart.

intros  n p;destruct (cm_correct n p);destruct (cm_correct p n);
  split;try discriminate;auto;intros;
  try subst p;intros;elimtype False; omega.
Qed.










 

