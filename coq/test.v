Require Import Arith.
Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.
Open Scope N_scope.

Locate "_ + _".

Check (3 * 4).

Print Scope nat_scope.

Check (3 * 4).

Check 33.
Check 33%nat.

Open Scope nat_scope.
Check 33.
Check (-12)%Z.

Check Zplus.
Check Z.add.


Open Scope Z_scope.
Section binomial_def.
  Variables a b:Z.
  Definition binomial z:Z := a*z + b.
    Section trinomial_def.
      Variable c : Z.
      Definition trinomial z:Z := (binomial z)*z + c.
    End trinomial_def.
End binomial_def.

Print binomial.

Section realization.
  Variables (A B :Set).
  Let spec : Set := (((A->B)->B)->B)->A->B.
  Let realization : spec
    := fun (f:((A->B)->B)->B) a => f (fun g => g a).

End realization.

Definition nat_fun_to_Z_fun  := (Z->Z)->Z->Z.

Open Scope nat.
Theorem le_i_SSi : forall i:nat, i <= S (S i).
Proof (fun i:nat => le_S _ _ (le_S _ _ (le_n i))).

Implicit Arguments le_S [n m].


Lemma id: forall A:Set ,A -> A.
Proof (fun (A : Set) (H : A) => H).

(* Proof. *)
(* intros. *)
(* apply H. *)
(* Qed. *)

Lemma diag: forall (A B :Set), (A->A->B)->A->B.
Proof (fun (A B : Set) (H : A -> A -> B) (H0 : A) => H H0 H0).
(* Proof. *)
(* intros A B. *)
(* intros. *)
(* apply H. *)
(* apply H0. *)
(* apply H0. *)
(* Qed. *)
(* refine ( *)
(* fun ( f:= fun x y =>   (x:A) (y: B) => f x y. *)
(* ) *)

