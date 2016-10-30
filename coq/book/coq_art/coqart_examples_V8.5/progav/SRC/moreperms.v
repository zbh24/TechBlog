Require Import List.
Set  Implicit Arguments.
 
Section perms.
Variable A : Set.
 
Inductive transpose : list A -> list A ->  Prop :=
  transpose_hd:
    forall (a b : A) (l : list A),  transpose (a :: (b :: l)) (b :: (a :: l))
 | transpose_tl:
     forall (a : A) (l l' : list A),
     transpose l l' ->  transpose (a :: l) (a :: l') .
 
Inductive perm (l : list A) : list A ->  Prop :=
  perm_id: perm l l
 | perm_tr:
     forall (l' l'' : list A), perm l l' -> transpose l' l'' ->  perm l l'' .
 
End perms.
Require Import Arith.
Check eq_nat_dec.
 
Fixpoint nb_occ (n : nat) (l : list nat) {struct l} : nat :=
 match l with
   nil => 0
  | p :: l' =>
      match eq_nat_dec n p with   left _ => S (nb_occ n l')
                                 | right _ => nb_occ n l' end
 end.
Print eq_nat_dec.
 
Lemma transpose_nb_occ:
 forall (l l' : list nat),
 transpose l l' -> forall (n : nat),  nb_occ n l = nb_occ n l'.
Proof.
intros l l' H; elim H; simpl.
intros a b l0 n; case (eq_nat_dec n a); case (eq_nat_dec n b); simpl; auto.
intros a l0 l'0 H0 H1 n; case (eq_nat_dec n a); simpl; auto.
Qed.
 
Lemma perm_nb_occ:
 forall (l l' : list nat),
 perm l l' -> forall (n : nat),  nb_occ n l = nb_occ n l'.
Proof.
intros l l' H; elim H; auto.
intros l'0; intros.
transitivity (nb_occ n l'0).
auto.
apply transpose_nb_occ; auto.
Qed.
 
Lemma not_perm: ~ perm (2 :: (3 :: (1 :: nil))) (3 :: (1 :: (1 :: nil))).
Proof.
intros abs.
generalize (perm_nb_occ abs 1).
simpl; discriminate 1.
Qed.
(* What follows is the solution to the last exercise proposed 
  in the chapter on reflexion.  It uses a computation of numbers
  of occurrences to decide that two lists are not equal. *)
 
Fixpoint eq_nat_bool (n1 n2 : nat) {struct n1} : bool :=
 match n1, n2 with
   0, 0 => true
  | S n1', S n2' => eq_nat_bool n1' n2'
  | _, _ => false
 end.
 
Fixpoint check_all_occs (l1 l2 l3 : list nat) {struct l3} : bool :=
 match l3 with
   nil => true
  | a :: tl =>
      if eq_nat_bool (nb_occ a l1) (nb_occ a l2) then check_all_occs l1 l2 tl
        else false
 end.
 
Theorem eq_nat_bool_false:
 forall n1 n2, eq_nat_bool n1 n2 = false ->  ~ n1 = n2.
induction n1; destruct n2; simpl; intros; discriminate || auto.
Qed.
 
Theorem check_all_occs_false:
 forall l1 l2 l3,
 check_all_occs l1 l2 l3 = false ->
  (exists n : nat , nb_occ n l1 <> nb_occ n l2 ).
intros l1 l2 l3; elim l3.
simpl; intros; discriminate.
intros n l IHl; simpl.
generalize (@eq_nat_bool_false (nb_occ n l1) (nb_occ n l2)).
case (eq_nat_bool (nb_occ n l1) (nb_occ n l2)).
auto.
intros; exists n; auto.
Qed.
 
Theorem check_all_occs_not_perm:
 forall l1 l2, check_all_occs l1 l2 l1 = false ->  ~ perm l1 l2.
intros l1 l2 Heq Hperm; elim (check_all_occs_false l1 l2 l1 Heq); intros n Hneq;
 elim Hneq; apply perm_nb_occ; assumption.
Qed.
 
Ltac
noperm := match goal with
          | |- ~ perm ?l1 ?l2 => apply check_all_occs_not_perm; reflexivity end.
 
Theorem not_perm2:
 ~ perm (1 :: (3 :: (2 :: nil))) (3 :: (1 :: (1 :: (4 :: (2 :: nil))))).
noperm.
Qed.
