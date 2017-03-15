Require Import NPeano.

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  -     reflexivity.
  -  simpl. rewrite -> IHn'. reflexivity.  Qed.


Lemma plus_comm: forall n m : nat,
  plus n  m = plus m  n.
Proof.
  intros n m. induction m as [ | m'].
    simpl. rewrite plus_0_r. reflexivity.
    simpl. rewrite <- IHm'. rewrite plus_n_Sm.
    reflexivity.
Qed.

Inductive bnat :=
  | BO : bnat
  | BT : bnat -> bnat
  | BA : bnat -> bnat
. 

Fixpoint bin_to_nat (b:bnat) :=
  match b with
      | BO => O
      | BT b' => (mult (bin_to_nat b') 2)
      | BA b' => S (mult (bin_to_nat b') 2)
  end.

Fixpoint incr (b:bnat) :=
  match b with
      | BO => BA BO
      | BT b' => BA b'
      | BA b' => BT (incr b')
  end.

Lemma equal0: forall b:bnat , S (bin_to_nat b) = bin_to_nat (incr b). 
Proof.
intros.
induction b.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. rewrite <- IHb. simpl.  reflexivity.
Qed.

(** Bin_To_Nat the nat to bin         *)
Fixpoint nat_to_bin (n:nat) :=
  match n with
      | O => BO
      | S n' => incr (nat_to_bin n')
  end.

Lemma conver_equal:forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
intros.
induction n.
- simpl. reflexivity.
- simpl. rewrite <- equal0. rewrite IHn. reflexivity.
Qed.

(* Lemma bin_to_nat_equal2: forall b, nat_to_bin (bin_to_nat b) = b. *)
(* Proof. *)
(* intros. *)
(* induction b as [ | b' H0 | b' H0]. *)
(* - simpl. reflexivity. *)
(* - simpl. *)
(* Abort. *)

Fixpoint zerob (b:bnat) :=
  match b with
      | BO => true
      | BT b' => zerob b'
      | BA b' => false
  end.

Fixpoint normalize (b:bnat) :=
  match b with
      | BO => BO
      | BT b' => match (zerob b') with
                     | true => BO
                     | false => BT (normalize b')
                 end
      | BA b' => BA (normalize b')
  end.


Lemma inc_bin: forall a, BT (incr a) = incr (incr (BT a) ).
Proof.
intros.
simpl.
reflexivity.
Qed.

Lemma zerob_norm_inv: forall b, zerob (normalize b) = zerob b.
Proof.
intros.
induction b.
-  simpl. reflexivity.
- simpl. destruct (zerob  b) eqn:IHZ. simpl. reflexivity.
  simpl. rewrite IHb.  reflexivity. 
- simpl. reflexivity.
Qed.

Lemma normalize_determinsic: forall b ,normalize (normalize b) = normalize b.
Proof.
intros.
induction b.
- simpl.
  reflexivity.
- simpl. 
  destruct (zerob b) eqn:IHZ.
  reflexivity.
  simpl.
  rewrite zerob_norm_inv.
  rewrite IHZ.
  rewrite IHb.
  reflexivity.
- 
  simpl.
  rewrite IHb.
  reflexivity.
Qed.

Lemma z_norm_true: forall b,zerob b = true -> normalize b = BO.
Proof.
intros.
induction b.
- simpl. reflexivity.
- 
 simpl in H.
 simpl.
 rewrite H.
 reflexivity.
- 
  simpl in H.
  discriminate.
Qed.

Lemma mult_comm:forall n m, mult n m = mult m n.
Proof.
Admitted.

Lemma z_bin_true: forall b, zerob b = true -> bin_to_nat b = O.
Proof.
induction b.
-
  simpl.
  intros.
  reflexivity.
-
  simpl.
  intros.
  rewrite (mult_comm).
  simpl.
  rewrite plus_0_r.
  rewrite (IHb H).
  simpl.
  reflexivity.
-
  simpl.
  intros.
  discriminate.
Qed.

Lemma normallize_incr: forall b, normalize (incr b) = incr (normalize b).
Proof.
intros.
induction b.
 
  simpl.
  reflexivity.
 
  simpl.
  destruct (zerob b) eqn: IHZ.
  simpl.
  rewrite (z_norm_true b IHZ).
  reflexivity. 

  simpl.
  reflexivity.
 
  simpl.
  assert(IHX: forall b1, zerob (incr b1) = false).
    intros.
    induction b1.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    assumption.
  rewrite (IHX b).
  rewrite IHb.
  reflexivity.
Qed.

Lemma double_norm: forall a, nat_to_bin (a + a) = normalize (BT (nat_to_bin a)).
Proof.
intros.
induction a.
- simpl. reflexivity.
- simpl (nat_to_bin (S a)).  simpl (nat_to_bin (S a + S a)).
  rewrite (plus_comm).
  simpl (nat_to_bin (S a + a)).
  rewrite inc_bin.
  rewrite IHa.
  rewrite normallize_incr.
  rewrite normallize_incr.
  reflexivity.
Qed.

Lemma bin_to_nat2: forall b,nat_to_bin (bin_to_nat (normalize b) ) = normalize b. 
Proof.
intros.
induction b.
- simpl. reflexivity.
- simpl. destruct (zerob b) eqn:H1. 
    simpl. reflexivity.
    simpl. rewrite (mult_comm).
    simpl. rewrite plus_0_r.
    rewrite double_norm.
    rewrite IHb.
    simpl.
    rewrite zerob_norm_inv.
    rewrite H1.
    rewrite normalize_determinsic.
    reflexivity.
-   simpl.
    rewrite mult_comm.
    simpl. rewrite plus_0_r.
    rewrite double_norm.
    rewrite IHb.
    rewrite <- normallize_incr.
    simpl.
    rewrite normalize_determinsic.
    reflexivity.
Qed.