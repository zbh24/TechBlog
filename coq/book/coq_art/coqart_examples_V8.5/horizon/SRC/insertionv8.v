(* A sorting example : 
   (C) Yves Bertot, Pierre Castéran 
*)

Require Import List.
Require Import ZArith.
Open Scope Z_scope.

Inductive sorted : list Z -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall z:Z, sorted (z :: nil)
  | sorted2 :
      forall (z1 z2:Z) (l:list Z),
        z1 <= z2 ->
        sorted (z2 :: l) -> sorted (z1 :: z2 :: l).

Hint Resolve sorted0 sorted1 sorted2 : sort.

Lemma sort_2357 :
 sorted (2 :: 3 :: 5 :: 7 :: nil).
Proof.
 auto with sort zarith.
Qed.


Theorem sorted_inv :
 forall (z:Z) (l:list Z), sorted (z :: l) -> sorted l.
Proof.
 intros z l H.
 inversion H; auto with sort.
Qed.

(*  Number of occurrences of z in l *)

Fixpoint nb_occ (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') =>
      match Z_eq_dec z z' with
      | left _ => S (nb_occ z l')
      | right _ => nb_occ z l'
      end
  end.

Eval compute in (nb_occ 3 (3 :: 7 :: 3 :: nil)).

Eval compute in (nb_occ 36725 (3 :: 7 :: 3 :: nil)).


(* list l' is a permutation of list l *)

Definition equiv (l l':list Z) := 
    forall z:Z, nb_occ z l = nb_occ z l'.

(* equiv is an equivalence ! *)

Lemma equiv_refl : forall l:list Z, equiv l l.
Proof.
 unfold equiv; trivial.
Qed.

Lemma equiv_sym : forall l l':list Z, equiv l l' -> equiv l' l.
Proof.
  unfold equiv; auto.
Qed.

Lemma equiv_trans :
 forall l l' l'':list Z, equiv l l' -> 
                         equiv l' l'' -> 
                         equiv l l''.
Proof.
 intros l l' l'' H H0 z.
 eapply trans_eq; eauto.
Qed.



Lemma equiv_cons :
 forall (z:Z) (l l':list Z), equiv l l' -> 
                             equiv (z :: l) (z :: l').
Proof.
 intros z l l' H z'.
 simpl; case (Z_eq_dec z' z); auto. 
Qed.


Lemma equiv_perm :
 forall (a b:Z) (l l':list Z),
   equiv l l' -> 
   equiv (a :: b :: l) (b :: a :: l').
Proof.
 intros a b l l' H z; simpl.
 case (Z_eq_dec z a); case (Z_eq_dec z b); 
  simpl; case (H z); auto.
Qed.

Hint Resolve equiv_cons equiv_refl equiv_perm : sort.


(* insertion of z into l at the right place 
   (assuming l is sorted) 
*)

Fixpoint aux (z:Z) (l:list Z) {struct l} : list Z :=
  match l with
  | nil => z :: nil
  | cons a l' =>
      match Z_le_gt_dec z a with
      | left _ =>  z :: a :: l'
      | right _ => a :: (aux z l')
      end
  end.
   

Eval compute in (aux 4 (2 :: 5 :: nil)).

Eval compute in (aux 4 (24 :: 50 ::nil)).

(* the aux function seems to be a good tool for sorting ... *)

Lemma aux_equiv : forall (l:list Z) (x:Z), 
                  equiv (x :: l) (aux x l).
Proof.
 induction l as [|a l0 H]; simpl ; auto with sort.
 intros x; case (Z_le_gt_dec x a);
   simpl; auto with sort.
 intro; apply equiv_trans with (a :: x :: l0); 
   auto with sort.
Qed.


Lemma aux_sorted :
 forall (l:list Z) (x:Z), sorted l -> sorted (aux x l).
Proof.
 intros l x H; elim H; simpl; auto with sort.
 intro z; case (Z_le_gt_dec x z); simpl; 
   auto with sort zarith.
 intros z1 z2; case (Z_le_gt_dec x z2); simpl; intros;
  case (Z_le_gt_dec x z1); simpl; auto with sort zarith.
Qed.

(* the sorting function *)

Definition sort :
  forall l:list Z, {l' : list Z | equiv l l' /\ sorted l'}.
 induction l as [| a l IHl]. 
 exists (nil (A:=Z)); split; auto with sort.
 case IHl; intros l' [H0 H1].
 exists (aux a l'); split.
 apply equiv_trans with (a :: l'); auto with sort.
 apply aux_equiv.
 apply aux_sorted; auto.
Defined.

Extraction "insert-sort" aux sort.


