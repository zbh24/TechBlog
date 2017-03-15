(*
 *  Seplog is an implementation of separation logic (an extension of Hoare
 *  logic by John C. Reynolds, Peter W. O'Hearn, and colleagues) in the
 *  Coq proof assistant (version 8, http://coq.inria.fr) together with a
 *  sample verification of the heap manager of the Topsy operating system
 *  (version 2, http://www.topsy.net). More information is available at
 *  http://staff.aist.go.jp/reynald.affeldt/seplog.
 *
 *  Copyright (c) 2005, 2006 Reynald Affeldt and Nicolas Marti
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *)

Require Import EqNat.
Require Import Bool.
Require Import ZArith.
Require Import List.
Require Import Classical.
Require Import Max.

(* lemmas on booleans and integers *)

Lemma beq_dif_false : forall n m, n <> m -> beq_nat n m = false.
  double induction n m; try tauto.
  simpl; intuition.
Qed. 

Lemma beq_nat_false : forall a b, beq_nat a b = false -> a <> b.
  double induction a b; simpl; auto.
  intro X; discriminate X.
Qed.

Lemma beq_nat_true: forall x y, beq_nat x y = true -> x = y.
  double induction x y; intros; auto.
  discriminate.
  discriminate.
Qed.

Lemma beq_nat_classic : forall a b,
  beq_nat a b = true \/ beq_nat a b =false.
  double induction a b; intros; simpl; auto.
Qed.

Lemma beq_nat_com: forall n m, beq_nat n m = beq_nat m n.
  double induction n m; simpl; auto.
Qed.

Lemma negb_false_is_true : forall x, negb x = false -> x = true.
  destruct x; auto.
Qed.

Lemma negb_true_is_false : forall x, negb x = true -> x = false.
  destruct x; auto.
Qed.

Lemma plus_lt_exists: forall l l' L, l' + l <= L -> exists n, L = n + l' + l.
  intros.
  assert (L = l + l' \/ L > l + l'); try omega.
  inversion_clear H0.
  exists 0.
  omega.
  exists (L - l - l').
  omega.
Qed.

(* lemmas on Z *)

Lemma Zeq_bool_classic : forall x y,
  Zeq_bool x y = true \/ Zeq_bool x y = false.
  intros; elim Zeq_bool; auto.
Qed.

Lemma Zeq_bool_refl : forall x, Zeq_bool x x = true.
  intros.
  unfold Zeq_bool.
  rewrite Zcompare_refl.
  auto.
Qed.

Lemma Zeq_bool_sym : forall x y, Zeq_bool x y = Zeq_bool y x.
  intros.
  unfold Zeq_bool.
  generalize (Ztrichotomy_inf x y); intro X; inversion_clear X.
  inversion_clear H.
  generalize (Ztrichotomy_inf y x); intro X; inversion_clear X.
  inversion_clear H.
  rewrite H0; rewrite H1; auto.
  subst x.
  generalize (Zlt_irrefl y); tauto.
  rewrite H0; rewrite H; auto.
  subst y.
  reflexivity.
  generalize (Ztrichotomy_inf y x); intro X; inversion_clear X.
  inversion_clear H0.
  rewrite H; rewrite H1; auto.
  subst y.
  generalize (Zlt_irrefl x); tauto.
  rewrite H0; rewrite H; auto.
Qed.

Lemma Zeq_bool_true : forall x y, Zeq_bool x y = true -> x = y.
  unfold Zeq_bool.
  intros x y.
  generalize (Ztrichotomy_inf x y); intro.
  inversion_clear H.
  inversion_clear H0.
  rewrite H.
  intro; discriminate.
  auto.
  rewrite H0.
  intro; discriminate.
Qed.

Lemma Zeq_bool_false : forall x y, Zeq_bool x y = false <-> x <> y.
  split; intros.
  generalize (Ztrichotomy_inf x y); intro X; inversion_clear X.
  inversion_clear H0.
  omega.
  subst x.
  rewrite Zeq_bool_refl in H; discriminate.
  omega.
  apply not_true_is_false.
  intro; apply H.
  apply Zeq_bool_true.
  assumption.
Qed.

Lemma Zeq_bool_false' : forall x y, Zeq_bool x y = false -> x <> y.
  intros.
  generalize (Zeq_bool_false x y); tauto.
Qed.

Lemma Zeq_bool_false'' : forall x y, x <> y -> Zeq_bool x y = false.
  intros.
  generalize (Zeq_bool_false x y); tauto.
Qed.

Lemma Zgt_bool_true : forall a b, Zgt_bool a b = true -> (a > b)%Z.
  intros.
  generalize (Z_gt_le_dec a b); intro X; inversion_clear X; auto.
  unfold Zgt_bool in H.
  red in H0.
  destruct (a ?= b)%Z; try discriminate||tauto.
Qed.

Lemma Zgt_bool_true' : forall a b, (a > b)%Z -> Zgt_bool a b = true.
  intros.
  unfold Zgt_bool.
  red in H.
  destruct (a ?= b)%Z; try auto||discriminate.
Qed.

Lemma Zgt_bool_false: forall a b, Zgt_bool a b = false -> (a <= b)%Z.
  intros.
  generalize (Z_gt_le_dec a b); intro X; inversion_clear X; auto.
  unfold Zgt_bool in H.
  red in H0.
  destruct (a ?= b)%Z; try discriminate||tauto.
Qed.

Lemma Zge_bool_true : forall a b, Zge_bool a b = true -> (a >= b)%Z.
  intros.
  generalize (Z_ge_lt_dec a b); intro X; inversion_clear X; auto.
  unfold Zge_bool in H.
  red in H0.
  destruct (a ?= b)%Z; try discriminate||tauto.
Qed.

Lemma Zge_bool_true' : forall a b, (a >= b)%Z -> Zge_bool a b = true.
  intros.
  unfold Zge_bool.
  red in H.
  destruct (a ?= b)%Z; auto.
Qed.

Lemma Zlt_bool_true : forall a b, Zlt_bool a b = true -> (a < b)%Z.
  intros.
  generalize (Z_lt_ge_dec a b); intro X; inversion_clear X; auto.
  unfold Zlt_bool in H.
  red in H0.
  destruct (a ?= b)%Z; try discriminate||tauto.
Qed.

Lemma Zlt_bool_Prop : forall a b, (a < b)%Z -> Zlt_bool a b = true.
  intros.
  red in H.
  unfold Zlt_bool.
  destruct (a ?= b)%Z; try discriminate||auto.
Qed.
  
Lemma Zlt_bool_Prop' : forall a b, (b >= a)%Z -> Zlt_bool b a = false.
  intros a b H.
  unfold Zlt_bool.
  generalize (Dcompare_inf (b ?= a))%Z; intro.
  inversion_clear H0.
  inversion_clear H1.
  rewrite H0; reflexivity.
  red in H.
  rewrite H0 in H.
  tauto.
  rewrite H1.
  auto.
Qed.

Lemma Zle_bool_true : forall a b, Zle_bool a b = true -> (a <= b)%Z.
  intros.
  generalize (Z_gt_le_dec a b); intro X; inversion_clear X; auto.
  unfold Zle_bool in H.
  red in H0.
  destruct (a ?= b)%Z; try discriminate||tauto.
Qed.

Lemma Zle_bool_true' : forall a b, (a <= b)%Z -> Zle_bool a b = true.
  intros.
  unfold Zle_bool.
  red in H.
  destruct (a ?= b)%Z; try discriminate||tauto.
Qed.

Lemma Zle_neq_lt : forall n m,
  (n <= m)%Z -> (n <> m)%Z -> (n < m)%Z.
  intros.
  omega.
Qed.

Lemma Z_of_nat_Zpos_P_of_succ_nat : forall n,
  Z_of_nat (n + 1) = Zpos (P_of_succ_nat n).
  intro.
  unfold Z_of_nat.
  destruct n.
  simpl.
  auto.
  simpl.
  generalize (nat_of_P_o_P_of_succ_nat_eq_succ n); intro.
  assert ((n + 1)%nat = (S n)).
  omega.
  rewrite H0.
  rewrite <-H.
  rewrite P_of_succ_nat_o_nat_of_P_eq_succ.
  auto.
Qed.

Lemma nat2pos: forall n,
  n > 0 ->
  exists p, Z_of_nat n = Zpos p /\ nat_of_P p = n.
  intros.
  destruct n.
  inversion H.
  simpl.
  exists (P_of_succ_nat n).
  split; auto.
  apply nat_of_P_o_P_of_succ_nat_eq_succ.
Qed.

Lemma Z_of_nat_inj : forall x y,
  Z_of_nat x = Z_of_nat y -> x = y.
  induction x.
  induction y; auto.
  simpl; intro X; discriminate X.
  induction y.
  simpl; intro X; discriminate X.
  intros.
  simpl in H.
  injection H; intro.
  rewrite <-nat_of_P_o_P_of_succ_nat_eq_succ.
  rewrite <-nat_of_P_o_P_of_succ_nat_eq_succ.
  rewrite H0.
  auto.
Qed.

Lemma Z_S : forall n,
  Z_of_nat (S n) = (Z_of_nat n + 1)%Z.
  intros.
  simpl.
  rewrite <-Z_of_nat_Zpos_P_of_succ_nat.
  rewrite inj_plus.
  simpl Z_of_nat.
  auto.
Qed.

(* TODO: c est deja dans la lib standard : Lemme inj_lt *)
Lemma Z_of_nat_inj': (forall x y, x = y -> Z_of_nat x = Z_of_nat y).
  auto.
Qed.

Lemma Z_of_nat_le_inj': forall x y, x <= y -> (Z_of_nat x <= Z_of_nat y)%Z.
  intros.
  omega.
Qed.

Lemma Z_of_nat_le_inj: forall x y, (Z_of_nat x <= Z_of_nat y)%Z -> x <= y.
  intros.
  omega.
Qed.

Lemma Z_of_nat_lt_inj': forall x y, x < y -> (Z_of_nat x < Z_of_nat y)%Z.
  intros.
  omega.
Qed.

Lemma Z_of_nat_lt_inj: forall x y, (Z_of_nat x < Z_of_nat y)%Z -> x < y.
  intros.
  omega.
Qed.

Lemma Z_of_nat_ge_inj': forall x y, x >= y -> (Z_of_nat x >= Z_of_nat y)%Z.
  intros.
  omega.
Qed.

Lemma Z_of_nat_ge_inj: forall x y, (Z_of_nat x >= Z_of_nat y)%Z -> x >= y.
  intros.
  omega.
Qed.

Lemma Z_of_nat_gt_inj': forall x y, x > y -> (Z_of_nat x > Z_of_nat y)%Z.
  intros.
  omega.
Qed.

Lemma Z_of_nat_gt_inj: forall x y, (Z_of_nat x > Z_of_nat y)%Z -> x > y.
  intros.
  omega.
Qed.

Lemma nat_of_Z: forall z,
  (z >= 0)%Z ->
  exists n, z = Z_of_nat n.
  destruct z.
  intros.
  exists 0.
  auto.
  intros.
  exists (nat_of_P p).
  eapply Zpos_eq_Z_of_nat_o_nat_of_P.
  intros.
  generalize (Zlt_neg_0 p).
  intros.
  contradiction.
Qed.

(* lemmas about lists *)

Lemma length_app : forall (A:Set) (l:list A) l', length (l++l') = plus (length l) (length l').
induction l.
simpl; auto.
simpl.
intro l'; rewrite (IHl l'); auto.
Qed.

Lemma tail_length : forall (A:Set) (lst:list A),
  length (tail lst) = (length lst - 1)%nat.
  induction lst; auto.
  simpl.
  rewrite <-minus_n_O.
  reflexivity.
Qed.

Lemma tail_app : forall (A:Set) (lst lst':list A),
  (0 < length lst)%nat ->
  tail (lst ++ lst') = tail lst ++ lst'.
  destruct lst; intros; auto.
  simpl in H; inversion H.
Qed.

Lemma incl_nil : forall (A:Set) (h:list A), incl h nil -> h=nil.
  induction h; auto.
  simpl; intros.
  red in H.
  assert (In a nil); [apply H; simpl; auto | idtac].
  simpl in H0; contradiction.
Qed.

Definition inter (A:Set) h1 h2 h := forall (x:A),
  In x h1 /\ In x h2 <-> In x h.
Implicit Arguments inter.

Lemma inter_nil: forall (A:Set) l, @inter A l nil nil.
  unfold inter; unfold In.
  tauto.
Qed.
Implicit Arguments inter_nil.

Lemma inter_weak : forall (A:Set) x L K M,
 @inter A K L M -> ~ In x K -> inter K (x :: L) M.
  intros.
  unfold inter.
  split; intros.
  elim (classic (x = x0)); intros.
  subst x0.
  generalize (H0 (proj1 H1)); contradiction.
  assert (In x0 L).
  inversion_clear H1.
  inversion H4.
  contradiction.
  auto.
  generalize (H x0); intuition; tauto.
  generalize (H x0); intro X; inversion_clear X.
  split; intuition.
Qed.
Implicit Arguments inter_weak.

Lemma inter_sym: forall (A:Set) h h1 h2,
  @inter A h h1 h2 -> inter h1 h h2.
  intros.
  red.
  intros.
  generalize (H x).
  tauto.
Qed.
Implicit Arguments inter_sym.

Lemma inter_nil_subset : forall (A:Set) (l:list A) l',
  inter l l' nil ->
  forall l'',
    incl l'' l ->
    inter l'' l' nil.
  intros.
  red.
  intros.
  split.
  intros.
  inversion_clear H1.
  red in H.
  generalize (H x); intro.
  inversion_clear H1.
  apply H4.
  split; auto.
  contradiction.
Qed.

Lemma inter_app : forall (A:Set) (l k m:list A), inter (l++k) m nil ->
  inter l m nil /\ inter k m nil.
  intros.
  red in H.
  split.
  split; intros.
  assert (In x (l++k)).
  apply in_or_app.
  intuition.
  generalize (H x); tauto.
  contradiction.
  split; intros.
  assert (In x (l++k)).
  apply in_or_app.
  intuition.
  generalize (H x); tauto.
  contradiction.
Qed.

Lemma inter_stren : forall (A:Set) (hd1:A) tl1 l2, 
  inter (hd1::tl1) l2 nil -> inter tl1 l2 nil.
  intros.
  red; split; intros.
  red in H.
  generalize (H x); intro.
  inversion_clear H1.
  apply H2; split.
  simpl; intuition.
  intuition.
  simpl in H0; tauto.
Qed.
Implicit Arguments inter_stren.

Lemma list_split : forall (A:Set) (l:list A) x,
  In x l ->
  exists l1, exists l2, l = l1 ++ (x::nil) ++ l2.
  induction l.
  simpl.
  intuition.
  intros.
  simpl.
  simpl in H.
  inversion_clear H.
  subst a.
  exists (@nil A).
  exists l.
  auto.
  generalize (IHl _ H0).
  simpl.
  intros.
  inversion_clear H.
  inversion_clear H1.
  exists (a::x0); exists x1.
  simpl.
  rewrite H.
  auto.
Qed.

Lemma list_split2 : forall (A:Set) (l:list A) k,
  (k <= length l)%nat ->
  exists l1, exists l2, length l1 = k /\
    l = l1 ++ l2.
  induction l.
  intros.
  simpl in H.
  inversion H.
  subst k.
  exists (@nil A).
  exists (@nil A).
  auto.
  intros.
  destruct k.
  exists (@nil A).
  exists (a::l).
  auto.
  simpl in H.
  assert (k <= length l)%nat.
  omega.
  generalize (IHl _ H0); intro X; inversion_clear X.
  inversion_clear H1.
  exists (a::x).
  simpl.
  exists x0.
  split.
  omega.
  rewrite (proj2 H2).
  reflexivity.
Qed.

(* permutations and accompanying lemmas *)

Set Implicit Arguments.

Inductive permut (A:Set) : (list A) -> (list A) -> Prop :=
  permut_refl: forall h, permut h h
  | permut_cons: forall a l0 l1, permut l0 l1 -> permut (a::l0) (a::l1)
  | permut_append: forall a l, permut (a::l) (l ++ a::nil)
  | permut_trans: forall l0 l1 l2, permut l0 l1 -> permut l1 l2 -> permut l0 l2.

Lemma permut_sym : forall (A:Set) (h1 h2 : (list A)), 
  permut h1 h2 -> permut h2 h1.
  intros.
  induction H.
  apply permut_refl.
  apply permut_cons.
  auto.
  generalize a; clear a.
  induction l.
  simpl.
  intro.
  apply permut_refl.
  simpl.
  intros.
  assert (permut (a::l ++ a0::nil) (a::a0::l)).
  apply permut_cons; auto.
  apply permut_trans with (a::a0::l); auto.
  apply permut_trans with (a0::(l ++ (a::nil))).
  apply permut_append with (a:=a) (l:=(a0::l)).
  apply permut_cons.
  apply IHl.
  apply permut_trans with l1; auto.
Qed.

Lemma permut_nil' : forall (A:Set) (k k':(list A)), 
  permut k k' -> k'=nil -> k=nil.
  do 4 intro.
  induction H; auto.
  intro X; discriminate X.
  intro X.
  destruct l.
  discriminate X.
  discriminate X.
Qed.

Lemma permut_nil : forall (A:Set) (k:(list A)), 
  permut k nil -> k=nil.
  intros.
  eapply permut_nil'.
  apply H.
  auto.
Qed.

Lemma In_permut : forall (A:Set) (h h':(list A)), permut h' h -> 
  forall x, In x h -> In x h'.
  do 4 intro.
  induction H.
  auto.
  intros.
  simpl; simpl in H0.
  inversion_clear H0; auto.
  simpl.
  intros.
  generalize (in_app_or _ _ _ H); intros.
  inversion_clear H0; auto.
  simpl in H1.
  inversion_clear H1; auto.
  contradiction.
  auto.
Qed.

Lemma permut_head : forall (A:Set) h (a b:A), permut (a::b::h) (b::a::h).
  intros.
  apply permut_trans with ((a::h) ++ b::nil).
  simpl.
  apply permut_cons.
  apply permut_append.
  apply permut_sym.
  apply permut_append with (l:=a::h) (a:=b).
Qed.

Lemma rotate_is_permut : forall (A:Set) k (a:A), (permut (a::k) (k++a::nil)).
  induction k.
  simpl; intros; apply permut_refl.
  intros.
  simpl.
  apply permut_trans with (a::a0::k).
  apply permut_head.
  apply permut_cons.
  auto.
Qed.

Lemma permut_inter : forall (A:Set) (k m:(list A)), permut k m -> 
  forall n p, inter n m p -> inter n k p.
  do 4 intro.
  induction H.
  auto.
  intros.
  red.
  intro.
  generalize (H0 x); intro X; inversion_clear X.
  split; intros.
  apply H1.
  inversion_clear H3.	
  split; auto.
  simpl in H5.
  inversion_clear H5.
  subst x.
  simpl; auto.
  simpl.
  right.
  apply In_permut with l0; auto.
  apply permut_sym; auto.
  generalize (H2 H3); intro X; inversion_clear X.
  split; auto.
  simpl in H5; inversion_clear H5.
  subst x.
  simpl; auto.
  simpl; right.
  apply In_permut with l1; auto.
  intros.
  red; intro.
  generalize (H x); intro X; inversion_clear X.
  split; intros.
  apply H0.
  inversion_clear H2.
  split; auto.
  simpl in H4; inversion_clear H4.
  subst x.
  apply In_permut with (a::l).
  apply permut_sym.
  apply rotate_is_permut.
  simpl; auto.
  apply in_or_app; auto.
  generalize (H1 H2); intro X; inversion_clear X.
  generalize (in_app_or _ _ _ H4); intro X; inversion_clear X.
  simpl; auto.
  simpl in H5; inversion_clear H5.
  subst x; simpl; auto.
  contradiction.
  auto.
Qed.

Ltac Permut n :=
  match goal with
  |  |- (permut ?X1 ?X1) => apply permut_refl
  |  |- (permut (?X1 :: ?X2) (?X1 :: ?X3)) =>
      let newn := eval compute in (length X2) in
      (apply permut_cons; Permut newn)
  |  |- (permut (?X1 :: ?X2) ?X3) =>
      match eval compute in n with
      | 1 => fail
      | _ =>
          let l0' := constr:(X2 ++ X1 :: nil) in
          (apply (@permut_trans _ (X1 :: X2) l0' X3);
            [ apply permut_append | compute; Permut (pred n) ])
      end
  end. 

Ltac PermutProve :=
  match goal with
  |  |- (permut ?X1 ?X2) =>
      match eval compute in (length X1 = length X2) with
      | (?X1 = ?X1) => Permut X1
      end
  end.

Lemma permut_inv_head : forall (A:Set) (L:list A) (c d:A), permut (c :: d :: L) (d :: c :: L).
  intros.
  apply permut_trans with (l1 := (c :: L) ++ d :: nil).
  simpl.
  apply permut_cons.
  apply permut_append.
  apply permut_sym.
  apply permut_append with (l := c :: L) (a := d).
Qed.

Lemma permut_app_com : forall (A:Set) (L K:(list A)), permut (L ++ K) (K ++ L).
intro.
induction L.
intro.
simpl.
rewrite <- app_nil_end.
apply permut_refl.
intro.
generalize (IHL (a :: K)); intro.
simpl.
simpl in H.
apply permut_trans with (l1 := a :: K ++ L).
apply permut_cons.
apply IHL.
induction K.
simpl.
apply permut_refl.
simpl.
apply permut_trans with (l1 := a0 :: a :: K ++ L).
apply permut_inv_head.
apply permut_cons.
apply IHK.
generalize (IHL (a :: K)); intro.
simpl in H0.
auto.
Qed.

Unset Implicit Arguments.

Definition length_rev : forall (A:Set) (l:list A), length (rev l) = length l.
  induction l; auto.
  simpl.
  rewrite length_app. 
  simpl.
  rewrite IHl.
  rewrite plus_comm.
  reflexivity.
Qed.

Lemma rev_inj : forall (A:Set) (l k:list A),
  rev l = rev k -> l = k.
  induction l; simpl; intros.
  destruct k; auto.
  assert (length (rev (a::k)) = O).
  rewrite <-H; auto.
  simpl in H0.
  rewrite length_app in H0.
  destruct (rev k); discriminate.
  destruct k.
  destruct (rev l); discriminate.
  simpl in H.
  generalize (app_inj_tail _ (rev k) _ a0 H); intros.
  rewrite (IHl k).
  intuition.
  subst a0; auto.
  intuition.
Qed.

Lemma list_last : forall (A:Set) (lst:list A), length lst > O ->
  exists lst', exists a, 
    lst = lst' ++ a::nil. 
  induction lst.
  simpl.
  intros.
  inversion H.
  intros.
  destruct lst.
  exists (@nil A).
  exists a.
  auto.
  assert ( length (a0::lst) > 0 ).
  simpl.
  omega.
  generalize (IHlst H0); intro.
  inversion_clear H1.
  inversion_clear H2.
  exists (a::x).
  exists x0.
  simpl.
  rewrite H1.
  auto.
Qed.

Lemma nth_app : forall (A:Set) n (lst:list A) (v:A),
  length lst <= n -> forall lst',
    nth n (lst++lst') v = nth (n-length lst) lst' v.
  induction n.
  intros.
  simpl.
  destruct lst.
  auto.
  inversion H.
  intros.
  destruct lst.
  auto.
  simpl app.
  simpl minus.
  simpl.
  rewrite <- IHn.
  auto.
  simpl in H; omega.
Qed.

Definition last (A:Set) (lst:list A) (def:A) := 
  match length lst with
    O => def
    | S n => nth n lst def
  end.
Implicit Arguments last.

(* delete the first n elements of a list *)
Fixpoint del_heads (A:Set) (l: list A) (n: nat) {struct n} : list A :=
  match n with
    0 => l
    | S n' => match l with
                nil => nil
                | hd::tl => del_heads A tl n'
              end
  end.
Implicit Arguments del_heads.

Lemma del_heads_length: forall n (A:Set) (l: list A), 
  length (del_heads l n) = length l - n.
  induction n; intros; simpl; try omega.
  destruct l; simpl; intuition.
Qed.
Implicit Arguments del_heads_length.

Lemma del_heads_plus : forall (A:Set) a b (lst:list A),
  del_heads lst (a + b) = del_heads (del_heads lst a) b.
  induction a; induction b; intros; auto.
  destruct lst; simpl; auto.
  destruct lst; auto.
  simpl (del_heads (a0::lst) (S a)).
  rewrite <-IHa.
  auto.
Qed.

Lemma del_heads_app' : forall n (A:Set) (lst lst':list A),
  length lst = n ->
  forall k, k <= n ->
    del_heads (lst ++ lst') k = (del_heads lst k) ++ lst'.
  induction n; intros.
  destruct lst; try discriminate.
  simpl.
  destruct k; auto.
  inversion H0.
  destruct lst; try discriminate.
  simpl in H; injection H; clear H; intro.
  simpl.
  destruct k; auto.
  simpl.
  apply IHn; omega.
Qed.

Lemma del_heads_app: forall n (A:Set) (l l':list A),
  length l = n ->
  del_heads (l ++ l') n = l'.
  intros.
  rewrite (del_heads_app' (length l)); try omega.
  assert (length (del_heads l n) = 0).
  rewrite del_heads_length.
  omega.
  destruct (del_heads l n); try discriminate || auto.
Qed.
Implicit Arguments del_heads_app.

Lemma del_heads_all : forall n (A:Set) (lst:list A),
  length lst = n ->
  del_heads lst n = nil.
  induction n; intros.
  simpl.
  destruct lst; try discriminate||auto.
  destruct lst; try discriminate.
  simpl.
  rewrite IHn.
  auto.
  simpl in H.
  injection H; auto.
Qed.

(* pickup the first n elements of a list *)
Fixpoint heads (A: Set) (l: list A) (n: nat) {struct n} : list A :=
  match n with
    0 => nil
    | S n' => match l with
                nil => nil
                | hd::tl => hd::heads A tl n'
	      end
  end.
Implicit Arguments heads.

Lemma length_heads : forall n (A:Set) (lst:list A) k,
  length lst = n ->
  k <= n ->
  length (heads lst k) = k.
  induction n; intros.
  destruct lst; try discriminate.
  destruct k.
  auto.
  inversion H0.
  destruct lst; try discriminate.
  simpl in H; injection H; clear H; intro.
  destruct k.
  auto.
  simpl.
  rewrite IHn; auto.
  omega.
Qed.

Lemma heads_app : forall n (A:Set) (lst1:list A),
  length lst1 = n ->
  forall lst2,
    heads (lst1 ++ lst2) n = lst1.
  induction n.
  intros.
  destruct lst1; try discriminate.
  auto.
  intros.
  destruct lst1; try discriminate.
  simpl in H.
  injection H; clear H; intro.
  simpl.
  rewrite IHn.
  reflexivity.
  auto.
Qed.

Lemma heads_del_heads : forall (A:Set) n (lst:list A),
  length lst = n ->
  forall k, k <= n ->
    lst = heads lst k ++ del_heads lst k.
  induction n.
  intros.
  destruct k.
  auto.
  inversion H0.
  intros.
  destruct k.
  auto.
  destruct lst; try discriminate.
  simpl.
  simpl in H; injection H; clear H; intro X; rewrite <-(IHn lst X k).
  auto.
  omega.
Qed.

(*
 * lemmas on nat
 *) 

Lemma mult_minus_distr_r : forall n m p, n >= m -> (n - m) * p = n * p - m * p.
  intuition.
Qed.

Lemma mult_minus_distr_l : forall n m p, m >= p -> n * (m - p) = n * m - n * p.
  intros.
  assert (n * (m - p) = (m - p) * n).
  intuition.
  rewrite H0.
  rewrite mult_minus_distr_r.
  intuition.
  intuition.
Qed.

(*
 * lemmas on max
 *)

Lemma max_lemma1: forall x1 x2 x3,
   x1 >= x2 ->
   max x1 x3 >= max x2 x3.
   intros.
   generalize (max_dec x1 x3); intro X; inversion_clear X.
   generalize (max_dec x2 x3); intro X; inversion_clear X.
   rewrite H0; rewrite H1.
   auto.
   rewrite H0; rewrite H1.
   generalize (le_max_r x1 x3); intros.
   rewrite H0 in H2.
   omega.
   generalize (max_dec x2 x3); intro X; inversion_clear X.
   rewrite H0; rewrite H1.
   generalize (le_max_l x1 x3); intros.
   rewrite H0 in H2.
   omega.
   rewrite H0; rewrite H1.
   omega.
Qed.

Lemma max_lemma2: forall x1 x2 x3,
   x1 > max x2 x3 ->
   x1 > x2 /\ x1 > x3.
   intros.
   generalize (max_dec x2 x3); intro X; inversion_clear X.
   split.
   omega.
   generalize (le_max_r x2 x3); intros.
   omega.
   split.
   generalize (le_max_l x2 x3); intros.
   omega.
   omega.
Qed.   

Lemma max_lemma3: forall x1 x2 x3,
  x1 > x2 /\ x1 > x3 ->
  x1 > max x2 x3.
  intros.
  inversion_clear H.
  generalize (max_dec x2 x3); intro X; inversion_clear X.
  omega.
  omega.
Qed.

Lemma max_lemma4: forall x y,
  max x y >= x.
  intros.
  generalize (le_max_l x y); auto.
Qed.

Lemma max_lemma5: forall x y z,
  z >= x ->
  max z y >= x.
  intros.
  generalize (le_max_l z y); omega.
Qed.

Lemma max_lemma6: forall x y z,
  z >= x ->
  max y z >= x.
  intros.
  generalize (le_max_r y z); omega.
Qed.

(*
 * definition of inequalities over naturals in bool (instead of Prop)
 *)

Fixpoint nat_lt (n m:nat) {struct n}: bool :=
  match n with 
    0 => match m with
           0 => false
           | S m' => true
         end
    | S n' => match m with
                0 => false
                | S m' => nat_lt n' m'
              end
  end.

Definition nat_le (n m:nat) : bool := orb (beq_nat n m) (nat_lt n m).

Fixpoint nat_gt (n m:nat) {struct n}: bool :=
  match n with 
    0 => false
    | S n' => match m with
                0 => true
                | S m' => nat_gt n' m'
              end
  end.

Definition nat_ge (n m:nat) : bool := orb (beq_nat n m) (nat_gt n m).

Lemma nat_lt_true: forall n m, nat_lt n m = true -> n < m.
  double induction n m.
  simpl; intro X; inversion X.
  intros.
  omega.
  simpl.
  intros.
  inversion H0.
  simpl; intros.
  cut (n1 < n0).
  omega.
  apply (H0 n0 H1).
Qed.

Lemma nat_lt_true': forall n m, n < m -> nat_lt n m = true.
  double induction n m.
  intro X; inversion X.
  intros.
  simpl.
  auto.
  simpl.
  intros.
  inversion H0.
  simpl; intros.
  assert (n1 < n0).
  omega.
  eapply H0; auto.
Qed.

Lemma nat_lt_false: forall n m, nat_lt n m = false -> n >= m.
  double induction n m.
  intuition.
  simpl; intros.
  inversion H0.
  simpl; intros.
  intuition.
  simpl; intros.
  cut (n1 >= n0).
  omega.
  apply H0; auto.
Qed.

Lemma nat_lt_false': forall n m, n >= m -> nat_lt n m = false.
  double induction n m.
  simpl; auto.
  simpl; intros.
  inversion H0.
  simpl; auto.
  simpl; intros.
  apply H0; omega.
Qed.

Lemma nat_lt_assym: forall n m, nat_lt n m = true -> nat_lt m n= false.
  intros.
  generalize (nat_lt_true _ _ H); intro.
  apply nat_lt_false'.
  intuition.
Qed.

Lemma nat_lt_irrefl: forall n , nat_lt n n = false.
  induction n.
  simpl; auto.
  simpl.
  auto.
Qed.

Lemma nat_lt_trans: forall n m p, nat_lt n m = true -> nat_lt m p = true -> nat_lt n p = true.
  intros.
  eapply nat_lt_true'.
  generalize (nat_lt_true _ _ H); intro.
  generalize (nat_lt_true _ _ H0); intro.
  intuition.
Qed.

Lemma nat_lt_classic: forall n m, nat_lt n m = true \/ nat_lt n m = false.
  intros.
  elim nat_lt; [left; auto | right; auto].
Qed.

Ltac Contrad_lt := intros; Hyp_lt_clean;
  match goal with
    | id: ?a = ?b |- _ => subst a; Contrad_lt
    | id: ?a < ?a |- _ => generalize (lt_irrefl a); tauto
    | id1: ?b < ?a, id': ?a < ?b |- _ => generalize (lt_asym a b); tauto
    | id1: ?b < ?a, id': ?a < ?b' |- _ => generalize (lt_trans b a b' id1 id'); clear id'; intros; Contrad_lt
    | |- _ => tauto
  end
  with Hyp_lt_clean :=
  match goal with
    | id: ?a = ?a |- _ => clear id; Hyp_lt_clean
    | id: ?a < ?b, id': ?a < ?b |- _ => clear id; Hyp_lt_clean
    | |- _ => idtac
  end.

(*****************************************************************************)
(* end of the part common with seplog, beginning of the part mips-specific   *)
(*****************************************************************************)

(* functions on nth *)

Lemma nth_beyond : forall (A:Set) (lst:list A) k dv,
  k < length lst ->
  forall lst',
    nth k lst dv = nth k (lst++lst') dv. 
induction lst.
destruct k.
simpl.
intros.
inversion H.
intros.
inversion H.
intros.
simpl in H.
destruct k.
auto.
simpl.
apply IHlst.
omega.
Qed.

Lemma list_tail' : forall (A:Set) (lst:list A) def_val,
  length lst > 0 ->
  nth 0 lst def_val :: tail lst = lst.
  destruct lst.
  simpl.
  intros.
  inversion H.
  intros.
  simpl.
  auto.
Qed.

Lemma list_split' : forall (A:Set) n (lst:list A) (def:A),
  length lst = n ->
  n > 0 ->
  forall j, j < n ->
    exists l1, length l1 = j /\ 
      exists l2,
	lst = l1 ++ (nth j lst def)::nil ++ l2.
induction n.
intros.
inversion H0.
intros.
destruct lst; try discriminate.
simpl in H; injection H; clear H; intro.
destruct n.
destruct lst; try discriminate.
destruct j.
simpl.
exists (@nil A).
split; auto.
exists (@nil A); auto.
inversion H1.
inversion H3.
destruct j.
simpl.
exists (@nil A); auto.
split; auto.
exists lst; auto.
assert (j < S n).
omega.
generalize (IHn _ def H (gt_Sn_O n) _ H2); intro X; inversion_clear X.
inversion_clear H3.
exists (a::x).
split; simpl; try omega.
inversion_clear H5.
exists x0.
pattern lst at 1.
rewrite H3.
split; auto.
Qed.

(*TODO: replace list_split' with list_split'', which is more general *)
Lemma list_split'' : forall (A:Set) n (lst:list A) (def:A),
  length lst = n ->
  forall j, j < n ->
    exists l1, length l1 = j /\ 
      exists l2,
	lst = l1 ++ (nth j lst def)::nil ++ l2.
induction n.
intros; destruct lst; try discriminate.
inversion H0.
intros; destruct lst; try discriminate.
simpl in H; injection H; clear H; intro.
destruct j.
exists (@nil A).
split; auto.
exists lst; auto.
simpl.
assert (j<n).
omega.
generalize (IHn _ def H _ H1); intro X; inversion_clear X as [l1].
inversion_clear H2.
inversion_clear H4 as [l2].
exists (a::l1).
split; simpl; auto.
exists l2.
simpl in H2.
rewrite <-H2.
reflexivity.
Qed.

Lemma list_last' : forall (A:Set) n (lst:list A) (def:A),
  length lst = n ->
  n > 0 ->
  exists l1, lst = l1 ++ (nth (n-1) lst def)::nil.
  intros.
  lapply (list_split' _ n lst def H H0 (n-1)).
  intros.
  inversion_clear H1.
  inversion_clear H2.
  inversion_clear H3.
  simpl in H2.
  rewrite H2 in H.
  rewrite length_app in H.
  simpl in H.
  assert (length x0 = 0).
  omega.
  destruct x0; try discriminate.
  exists x.
  intuition.
  omega.
Qed.

(* element deletion *)
(* del_nth the nth of lst (0 <= nth < length lst) *)

Fixpoint del_nth (A:Set) (n:nat) (lst:list A) { struct lst } : list A :=
  match lst with
    nil => nil
    | hd::tl => match n with
		  O => tl
		  | S n' => hd::del_nth A n' tl
		end
  end.
Implicit Arguments del_nth.

Lemma del_nth_length : forall (A:Set) (lst:list A) (n:nat),
  n < length lst ->
  length (del_nth n lst) = length lst - 1.
  induction lst; auto.
  intros.
  simpl in H.
  destruct n.
  simpl.
  omega.
  simpl.
  rewrite IHlst.
  omega.
  omega.
Qed.

Definition del_nth_last (A:Set) (lst:list A) : list A :=
  match lst with
    nil => nil
    | _ => del_nth ((length lst) - 1) lst
  end.
Implicit Arguments del_nth_last.

Lemma del_nth_last_length: forall (n:nat) (A:Set) (lst:list A),
  length lst = n ->
  length (del_nth_last lst) = (n - 1)%nat.
destruct n.
intros.
destruct lst; try discriminate.
simpl.
auto.
intros.
unfold del_nth_last.
destruct lst; try discriminate.
cutrewrite (length (a :: lst) - 1 = length lst).
rewrite del_nth_length.
omega.
simpl; omega.
simpl.
omega.
Qed.

Lemma del_nth_last_exact' : forall (A:Set) (lst:list A) (a:A),
  del_nth (length lst) (lst ++ a::nil) = lst.
  induction lst; auto.
  simpl.
  intros.
  rewrite IHlst.
  auto.
Qed.

Lemma del_nth_last_exact : forall (A:Set) (lst:list A) a,
  del_nth_last (lst ++ a::nil) = lst.
  intros.
  unfold del_nth_last.
  cutrewrite ( length (lst ++ a :: nil) - 1 = length lst ).
  rewrite del_nth_last_exact'.
  destruct lst; auto.
  simpl; rewrite length_app; simpl; omega.
Qed.

Lemma del_nth_app : forall (A:Set) k (lst1:list A),
  length lst1 = k ->
  forall lst a lst2,
    lst = lst1 ++ a::lst2 ->
    del_nth k lst = lst1 ++ lst2.
  induction k.
  intros.
  destruct lst1; try discriminate.
  rewrite H0.
  auto.
  intros.
  destruct lst1; try discriminate.
  simpl in H; injection H; clear H; intro.
  destruct lst; try discriminate.
  simpl in H0; injection H0; clear H0; intros; subst a1.
  simpl.
  rewrite (IHk lst1 H lst a lst2 H0); auto.
Qed.

(* list update *)

Fixpoint update_list (A:Set) (l:list A) (n:nat) (v:A) {struct l} : list A :=
  match l with
    nil => nil
    | hd::tl => match n with
		  O => v::tl
		  | S n' => hd :: update_list _ tl n' v
		end
  end.
Implicit Arguments update_list.

Lemma length_update_list : forall (A:Set) n lst k (v:A),
  length lst = n ->
  length (update_list lst k v) = n.
  induction n; intros.
  destruct lst; try discriminate.
  auto.
  destruct lst; try discriminate.
  simpl in H; injection H; clear H; intros.
  destruct k.
  simpl; omega.
  simpl.
  rewrite IHn; auto.
Qed.

Lemma update_list_out : forall (A:Set) n (m:A) lst,
  n >= length lst ->
  update_list lst n m = lst.
  induction n.
  intros.
  destruct lst; try discriminate.
  auto.
  simpl in H.
  inversion H.
  intros.
  destruct lst.
  auto.
  simpl.
  rewrite IHn.
  auto.
  simpl in H.
  omega.
Qed.

Lemma nth_update_list : forall (A:Set) n (m:A) lst def_val,
  n < length lst ->
  nth n (update_list lst n m) def_val = m.
  induction n.
  intros.
  destruct lst.
  inversion H.
  simpl.
  auto.
  intros.
  destruct lst.
  simpl in H.
  inversion H.
  simpl in H.
  assert (n < length lst).
  omega.
  simpl.
  rewrite IHn.
  auto.
  auto.
Qed.

Lemma nth_update_list' : forall (A:Set) lst n n' (m:A) def_val,
  n <> n' ->
  nth n (update_list lst n' m) def_val = nth n lst def_val.
  induction lst.
  intros.
  simpl.
  destruct n; auto.
  intros.
  destruct n.
  simpl.
  destruct n'.
  tauto.
  simpl.
  auto.
  simpl.
  destruct n'.
  simpl.
  auto.
  simpl.
  rewrite IHlst; auto.
Qed.

Lemma update_list_app : forall (A:Set) n lst (v:A),
  length lst <= n -> forall lst',
    update_list (lst++lst') n v = lst ++ (update_list lst' (n-length lst) v).
  induction n.
  intros.
  destruct lst.
  auto.
  inversion H.
  intros.
  destruct lst.
  auto.
  simpl.
  rewrite IHn.
  auto.
  simpl in H; omega.
Qed.

Lemma update_list_app' : forall (A:Set) n lst (v:A),
  n < length lst -> forall lst',
    update_list (lst++lst') n v = (update_list lst n v) ++ lst'.
  induction n.
  intros.
  destruct lst.
  inversion H.
  simpl.
  auto.
  intros.
  destruct lst.
  inversion H.
  simpl.
  rewrite IHn.
  auto.
  simpl in H; omega.
Qed.

Lemma del_nth_update_list : forall (A:Set) (lst:list A) k m,
  del_nth k (update_list lst k m) =
  del_nth k lst.
  induction lst.
  auto.
  intros.
  destruct k.
  auto.
  simpl.
  rewrite IHlst.
  auto.
Qed.


(*
 * about minus
 *)

Lemma minus_plus': forall n m p, p <= n -> m = n - p -> n = m + p.
  do 2 intro.
  generalize m; clear m.
  induction n.
  simpl.
  intros.
  subst m.
  simpl.
  destruct p.
  reflexivity.
  inversion H.
  intros.
  destruct p.
  rewrite <-minus_n_O in H0.
  subst m.
  rewrite <-plus_n_O.
  reflexivity.
  simpl in H0.
  rewrite plus_comm.
  simpl.
  rewrite plus_comm.
  rewrite <-IHn.
  reflexivity.
  apply le_S_n.
  assumption.
  assumption.
Qed.

Lemma minus_plus_comm : forall a b n p,
  p <= a ->
  a + n - p = b -> a - p + n = b.
  induction a.
  intros.
  inversion H.
  subst p.
  simpl.
  simpl in H0.
  rewrite <-minus_n_O in H0.
  assumption.
  intros.
  destruct p.
  rewrite <-minus_n_O in H0.
  rewrite <-minus_n_O.
  assumption.
  cutrewrite (S a - S p = a - p).
  apply IHa.
  apply le_S_n.
  assumption.
  cutrewrite (S a + n = S (a+n)) in H0.
  simpl in H0.
  assumption.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Lemma minus_le_plus : forall c a b,
  c - b <= a -> c <= a + b.
  induction c.
  intros.
  apply le_O_n.
  intros.
  destruct b.
  rewrite <-plus_n_O.
  rewrite <-minus_n_O in H.
  assumption.
  simpl in H.
  generalize (IHc _ _ H); intro.
  rewrite plus_comm.
  simpl.
  apply le_n_S.
  rewrite plus_comm.
  assumption.
Qed.

Lemma plus_le_minus : forall c a b,
  a + c <= b -> a <= b - c.
  induction c.
  intros.
  rewrite <-plus_n_O in H.
  rewrite <-minus_n_O.
  assumption.
  intros.
  destruct b.
  simpl.
  inversion H.
  destruct a.
  apply le_O_n.
  discriminate.
  simpl.
  apply IHc.
  apply le_S_n.
  rewrite plus_n_Sm.
  assumption.
Qed.

Lemma plus_le_minus' : forall c a b,
  a <= b + c -> a - c <= b.
  induction c.
  intros.
  rewrite <-plus_n_O in H.
  rewrite <-minus_n_O.
  assumption.
  intros.
  destruct a.
  simpl.
  apply le_O_n.
  simpl.
  apply IHc.
  apply le_S_n.
  rewrite plus_n_Sm.
  assumption.
Qed.

Lemma plus_lt_minus' : forall c a b,
  b > 0 ->
  a < b + c -> a - c < b.
  induction c.
  intros.
  rewrite <-plus_n_O in H0.
  rewrite <-minus_n_O.
  assumption.
  intros.
  destruct a.
  simpl.
  assumption.
  simpl.
  apply IHc.
  assumption.
  apply lt_S_n.
  rewrite plus_n_Sm.
  assumption.
Qed.

Lemma plus_lt_minus : forall c a b,
  a + c < b -> a < b - c.
  induction c.
  intros.
  rewrite <-plus_n_O in H.
  rewrite <-minus_n_O.
  assumption.
  intros.
  destruct b.
  simpl.
  inversion H.
  destruct a.
  simpl.
  apply IHc.
  simpl.
  simpl in H.
  apply lt_S_n.
  assumption.
  simpl.
  apply IHc.
  apply lt_S_n.
  rewrite plus_n_Sm.
  assumption.
Qed.

Lemma plus_minus_assoc : forall b a c,
  b >= c ->
  a + b - c = a + (b-c).
  induction b.
  simpl.
  intros.
  destruct c.
  rewrite <-minus_n_O.
  reflexivity.
  inversion H.
  intros.
  destruct c.
  simpl.
  rewrite <-minus_n_O.
  reflexivity.
  simpl.
  rewrite <-IHb.
  destruct a.
  simpl.
  reflexivity.
  simpl (S a + S b - S c).
  rewrite <-plus_n_Sm.
  rewrite (plus_comm (S a) b).
  rewrite <-plus_n_Sm.
  rewrite plus_comm.
  reflexivity.
  red.
  apply le_S_n.
  assumption.
Qed.

Lemma minus_minus_comm : forall a b n p,
  p + n <= a ->
  a - n - p = b -> a - p - n = b.
  intros.
  symmetry.
  apply plus_minus.
  symmetry.
  apply plus_minus.
  rewrite plus_assoc.
  rewrite plus_comm.
  rewrite plus_assoc.
  apply minus_plus'.
  apply le_trans with (p+n).
  rewrite plus_comm.
  apply le_plus_trans.
  constructor.
  assumption.
  symmetry.
  apply minus_plus'.
  apply plus_le_minus.
  assumption.
  symmetry.
  assumption.
Qed.

Lemma le2lt : forall n k,
  n < k -> n <= k - 1.
  intros.
  destruct k.
  inversion H.
  simpl.
  rewrite <-minus_n_O.
  red in H.
  apply le_S_n.
  assumption.
Qed.

Lemma minus_le_compat_l : forall n a b,
  n <= a ->
  n <= b ->
  a <= b -> a - n <= b - n.
  induction n.
  intros.
  rewrite <-minus_n_O.
  rewrite <-minus_n_O.
  assumption.
  intros.
  destruct a.
  inversion H.
  destruct b.
  inversion H1.
  simpl.
  apply IHn.
  apply le_S_n.
  assumption.
  apply le_S_n.
  assumption.
  apply le_S_n.
  assumption.
Qed.

Lemma minus_lt_compat : forall a n m,
  m < n ->
  n <= a ->
  a - n < a - m.
  induction a.
  intros.
  inversion H0.
  subst n.
  inversion H.
  intros.
  destruct n.
  inversion H.
  destruct m.
  rewrite <-minus_n_O.
  apply lt_minus.
  assumption.
  assumption.
  simpl.
  apply IHa.
  apply lt_S_n.
  assumption.
  apply le_S_n.
  assumption.
Qed.

Lemma minus_compat : forall a b a' b',
  a = a' ->
  b = b' -> 
  a - b = a' - b'.
  intros.
  subst a'.
  subst b'.
  reflexivity.
Qed.

Lemma plus_compat : forall a b a' b',
  a = a' ->
  b = b' -> 
  a + b = a' + b'.
  intros.
  subst a'.
  subst b'.
  reflexivity.
Qed.

(*
 * about le/lt
 *) 

Lemma scale_le : forall a,
  1 <= a ->
  forall b, 
    b <= a * b.
  intros.
  apply le_trans with (1*b).
  rewrite mult_1_l.
  constructor.
  apply mult_le_compat_r.
  assumption.
Qed.

Lemma scale_lt : forall a,
  1 < a ->
  forall b,
    1 <= b ->
    b < a * b.
  intros.
  apply le_lt_trans with (1*b).
  rewrite mult_1_l.
  constructor.
  apply mult_lt_compat_r.
  assumption.
  red.
  assumption.
Qed.

Lemma le_neq_lt : forall n m,
  n <= m -> n <> m -> n < m.
  induction n.
  intros.
  destruct m.
  tauto.
  red.
  apply le_n_S.
  apply le_O_n.
  intros.
  destruct m.
  inversion H.
  apply lt_n_S.
  apply IHn.
  apply le_S_n.
  assumption.
  intro.
  apply H0.
  subst n.
  reflexivity.
Qed.

Lemma my_mult_lt_compat_l: forall a b c,
  a * c < b * c ->
  c >= 1 ->
  a < b.
  double induction a b; simpl; intros.
  tauto.
  omega.
  inversion H0.
  cut (n0 < n).
  omega.
  assert (n0 * c < n * c).  
  omega.
  eapply H0.
  apply H3.
  auto.
Qed.

Lemma S_lt : forall k,
  k > 0 ->
  forall a b,
    a < b ->
    a * k < b * k.
  induction k.
  intros.
  inversion H.
  intros.
  destruct k.
  omega.
  cutrewrite (a*(S (S k)) = a * S k + a).
  cutrewrite (b*(S (S k)) = b * S k + b).
  apply lt_trans with (b * S k + a).
  apply plus_lt_compat_r.
  apply IHk.
  omega.
  auto.
  apply plus_lt_compat_l.
  auto.
  cutrewrite (S (S k) = S k + 1).
  rewrite mult_plus_distr_l.
  omega.
  omega.
  cutrewrite (S (S k) = S k + 1).
  rewrite mult_plus_distr_l.
  omega.
  omega.
Qed.

Lemma inv_lt : forall k a b,
  k > 0 -> 
  b > 0 ->
  a * k < b * k ->
  a < b.
  induction k.
  intros.
  inversion H.
  intros.
  destruct k.
  omega.
  apply IHk; auto.
  omega.
  cutrewrite (a*(S(S k)) = a * S k + a) in H1.
  cutrewrite (b*(S(S k)) = b * S k + b) in H1.
  assert (a = b \/ a > b \/ a < b ).
  omega.
  inversion_clear H2.
  subst a.
  omega.
  inversion_clear H3.
  omega.
  apply S_lt.
  omega.
  auto.
  cutrewrite (S (S k) = S k + 1).
  rewrite mult_plus_distr_l.
  omega.
  omega.
  cutrewrite (S (S k) = S k + 1).
  rewrite mult_plus_distr_l.
  omega.
  omega.
Qed.

Lemma tmp : forall n k a b,
  a < b ->
  a + n * b = k * b ->
  a = 0.
  induction n.
  intros.
  simpl in H0.
  rewrite <-plus_n_O in H0.
  destruct k.
  simpl in H0.
  assumption.
  cutrewrite (S k = 1 + k) in H0.
  rewrite mult_plus_distr_r in H0.
  rewrite mult_1_l in H0.
  destruct b.
  rewrite mult_0_r in H0.
  simpl in H0.
  assumption.
  assert (a >= S b).
  rewrite H0.
  red.
  apply le_plus_trans.
  constructor.
  assert (~ (a < S b)).
  omega.
  tauto.
  auto.
  intros.
  destruct k.
  simpl in H0.
  destruct a; auto.
  rewrite plus_Sn_m in H0.
  discriminate.
  intros.
  assert ( a + n * b = k * b ).
  cutrewrite (S n = 1 + n) in H0.
  cutrewrite (S k = 1 + k) in H0.
  rewrite mult_plus_distr_r in H0.
  rewrite mult_plus_distr_r in H0.
  rewrite mult_1_l in H0.
  omega.
  auto.
  auto.
  eapply IHn.
  apply H.
  apply H1.
Qed.

(**************************************)
(* definition and properties of power *)
(**************************************)

Fixpoint power (b:nat) (e:nat) {struct e} : nat :=
  match e with
    O => 1
    | S e' => b * (power b e')
  end.

Lemma power_0 : power 2 0 = 1.
  auto.
Qed.

Lemma power_1' : power 2 1 = 2.
  auto.
Qed.

Lemma power_2 : power 2 2 = 4.
  auto.
Qed.

Lemma power_3 : power 2 3 = 8.
  auto.
Qed.

Lemma power_8 : power 2 8 = 256.
  auto.
Qed.

Lemma power_1 : forall n, 1 <= power 2 n.
  induction n; simpl; omega.
Qed.

Lemma power_S : forall k n, power k (S n) = k * power k n.
  auto.
Qed.

Lemma two_power_nat_power : forall l,
  two_power_nat l = Z_of_nat (power 2 l).
  induction l; simpl; intros; intuition.
  rewrite two_power_nat_S.
  rewrite <-plus_n_O.
  rewrite IHl.
  rewrite inj_plus.
  omega.
Qed.

Lemma two_power_nat_is_exp : forall (n m:nat),
  (two_power_nat (n + m) = two_power_nat n * two_power_nat m)%Z.
  intros.
  repeat rewrite two_power_nat_correct.
  repeat rewrite Zpower_nat_is_exp.
  reflexivity.
Qed.

Lemma power_is_exp : forall (n m:nat),
  power 2 (n + m) = power 2 n * power 2 m.
  intros.
  apply Z_of_nat_inj.
  rewrite <-two_power_nat_power.
  rewrite two_power_nat_is_exp.
  rewrite inj_mult.
  rewrite <-two_power_nat_power.
  rewrite <-two_power_nat_power.
  auto.
Qed.

Lemma two_power_nat_1 : forall l:nat, (1 <= two_power_nat l)%Z.
  intro.
  rewrite two_power_nat_power.
  generalize (power_1 l); intro.
  omega.
Qed.

Lemma two_power_nat_lt : forall k l, l < k ->
  (two_power_nat l < two_power_nat k)%Z.
  induction k.
  intros.
  inversion_clear H.
  intros.
  inversion H.
  subst l.
  rewrite two_power_nat_S.
  assert (forall (z:Z), z >= 1 -> z < 2 * z)%Z.
  intros.
  omega.
  apply H0.
  generalize (two_power_nat_1 k); intro.
  omega.
  subst m.
  rewrite two_power_nat_S.
  assert (l < k)%nat.
  omega.
  generalize (IHk _ H0); intro.
  apply Zlt_trans with (two_power_nat k).
  auto.
  assert (forall (z:Z), z >= 1 -> z < 2 * z)%Z.
  intros.
  omega.
  apply H3.
  generalize (two_power_nat_1 k); intro.
  omega.
Qed.

Lemma two_power_nat_le : forall k l, l <= k ->
  (two_power_nat l <= two_power_nat k)%Z.
  induction k.
  intros.
  inversion_clear H.
  omega.
  intros.
  inversion H.
  subst l.
  omega.
  subst m.
  rewrite two_power_nat_S.
  generalize (IHk _ H1); intro.
  apply Zle_trans with (two_power_nat k).
  auto.
  assert (forall (z:Z), z >= 1 -> z <= 2 * z)%Z.
  intros.
  omega.
  apply H2.
  generalize (two_power_nat_1 k); intro.
  omega.
Qed.

Lemma power_2_gt : forall n m,
  n > m ->
  power 2 n > power 2 m.
  intros.
  apply Z_of_nat_gt_inj.
  repeat rewrite <-two_power_nat_power.
  cut (  two_power_nat m < two_power_nat n )%Z.
  omega.
  apply two_power_nat_lt.
  auto.
Qed.

Lemma power_2_lt : forall n m,
  n < m ->
  power 2 n < power 2 m.
  intros.
  assert (m > n).
  omega.
  generalize (power_2_gt _ _ H0); omega.
Qed.

Lemma power_2_ge : forall n m,
  n >= m ->
  power 2 n >= power 2 m.
  intros.
  apply Z_of_nat_ge_inj.
  repeat rewrite <-two_power_nat_power.
  cut (  two_power_nat m <= two_power_nat n )%Z.
  omega.
  apply two_power_nat_le.
  auto.
Qed.

Lemma power_2_le : forall n m,
  n <= m ->
  power 2 n <= power 2 m.
  intros n m0 H.
  assert (m0 >= n).
  omega.
  generalize (power_2_ge _ _ H0); omega.
Qed.

Lemma power_plus : forall n,
  power 2 n + power 2 n = power 2 (S n).
  simpl.
  auto.
Qed.

(********************************************)
(* definition and properties of beta = 2^32 *)
(********************************************)

Definition beta (e:nat) := power 2 (e * 32).

Lemma beta_is_exp : forall n m,
  beta (n + m) = beta n * beta m.
  unfold beta.
  intros.
  assert ((n + m) * 32 = n * 32 + m * 32).
  omega.
  rewrite H; clear H.
  rewrite power_is_exp.
  auto.
Qed.

Lemma beta_power : forall (e:nat), beta e = power 2 (e * 32).
  auto.
Qed.

Lemma beta_power1 : beta 1 = power 2 32.
  auto.
Qed.

Lemma power_64_beta : power 2 64 = beta 2.
  unfold beta.
  simpl (2*32).
  reflexivity.
Qed.

Lemma beta_1 : forall l, 1 <= beta l.
  intros.
  unfold beta.
  apply power_1.
Qed.

Lemma beta_gt : forall n m,
  n > m ->
  beta n > beta m.
  intros.
  unfold beta.
  apply power_2_gt.
  omega.
Qed.

Lemma beta_lt : forall m n,
  m < n ->
  beta m < beta n.
  intros.
  unfold beta.
  apply power_2_lt.
  omega.
Qed.

Lemma beta_ge : forall n m,
  n >= m ->
  beta n >= beta m.
  intros.
  unfold beta.
  apply power_2_ge.
  omega.
Qed.

Lemma beta_le : forall n m,
  n <= m ->
  beta n <= beta m.
  intros.
  unfold beta.
  apply power_2_le.
  omega.
Qed.

Lemma beta_1_2 : beta 1 >= 2.
  rewrite <-power_1'.
  rewrite beta_power1.
  apply power_2_ge.
  omega.
Qed.

Lemma beta_1_4 : beta 1 >= 4.
  rewrite <-power_2.
  rewrite beta_power1.
  apply power_2_ge.
  omega.
Qed.

Open Local Scope Z_scope.

(*
 * lemmas about Z
 *)

  Lemma Zminus_le_compat : forall a b c,
    a <= c -> a - b <= c - b.
    intros.
    omega.
  Qed.

Lemma Zplus_compat : forall a b a' b',
       a = a' -> b = b' -> (a + b) = (a' + b').
  intros.
  subst a; subst b'; reflexivity.
Qed.

Lemma Zlt_neg_pos : forall p q,
  (Zneg p < Zpos q)%Z.
  intros.
  red.
  generalize (Zle_neg_pos p q); intro.
  red in H.
  auto.
Qed.

Lemma coeff_unique' : forall a b k,
  0 < k ->
  -k < a < k ->
  -k < b < k ->
  a * k + b = 0 -> a = 0 /\ b = 0.
  intros.
  assert (a * k = - b).
  omega.
  generalize (Z_lt_ge_dec a 0); intro X; inversion_clear X.
  assert ( b > 0 ).
  assert ( -b < 0 ).
  rewrite <-H3.
  assert ( 0 < - (a * k) ).
  rewrite <-Zopp_mult_distr_l_reverse.
  apply Zmult_lt_0_compat.
  omega.
  omega.
  omega.
  omega.
  assert ( - k * k < a * k <= - k).
  split.
  apply Zmult_lt_compat_r.
  omega.
  omega.
  cutrewrite (-k = (-1)*k).
  apply Zmult_le_compat_r.
  omega.
  omega.
  omega.
  rewrite H3 in H6.
  assert (k <= b).
  omega.
  omega.
  generalize (Z_eq_dec a 0); intro X; inversion_clear X.
  split; auto.
  rewrite H5 in H3.
  simpl in H3.
  omega.
  assert (a > 0).
  omega.
  assert (b < 0).
  assert (0 < -b).
  rewrite <-H3.
  apply Zmult_lt_0_compat.
  omega.
  omega.
  omega.
  assert (k <= a * k < k * k).
  split.
  cutrewrite (k = 1 * k).
  apply Zmult_le_compat.
  omega.
  rewrite Zmult_1_l.
  omega.
  omega.
  omega.
  ring.
  apply Zmult_lt_compat_r.
  omega.
  omega.
  rewrite H3 in H8.
  assert (-k >= b).
  omega.
  assert (k <= b).
  omega.
  omega.
Qed.
  
Lemma coeff_unique : forall a b a' b' k,
  0 <= a < k /\ 0 <= b < k /\ 0 <= a' < k /\ 0 <= b' < k ->
  a * k + b = a' * k + b' -> a = a' /\ b = b'.
  intros.
  assert ((a-a')*k + (b-b') = 0).
  rewrite Zmult_minus_distr_r.
  omega.
  assert (0 < k).
  omega.
  assert (-k < a - a' < k).
  omega.
  assert (-k < b - b' < k).
  omega.
  generalize (coeff_unique' _ _ _ H2 H3 H4 H1); intro.
  split; omega.
Qed.

(*
 * Zpower
 *)

Fixpoint Zpower (b:Z) (e:nat) {struct e} : Z :=
  match e with
    O => 1
    | S e' => b * (Zpower b e')
  end.

Notation "b ^^ e" := (Zpower b e) (at level 30).

Lemma Zpower_S : forall k n, k^^(S n) = k * k^^n.
  auto.
Qed.

Lemma Zpower_is_exp : forall (n m: nat),
  Zpower 2 (n + m) = Zpower 2 n * Zpower 2 m.
  induction n.
  simpl plus.
  simpl Zpower.
  intros; ring.
  intros.
  simpl plus.
  do 2 rewrite Zpower_S.
  rewrite IHn.
  ring.
Qed.

Lemma Zpower_0 : forall n, 0 < Zpower 2 n.
  induction n.
  simpl.
  red.
  auto.
  rewrite Zpower_S.
  omega.
Qed.

Lemma Zpower_1 : forall n, 1 <= Zpower 2 n.
  induction n.
  simpl.
  omega.
  rewrite Zpower_S.
  omega.
Qed.


Lemma Zpower_2_le : forall n m,
  (n <= m)%nat ->
  Zpower 2 n <= Zpower 2 m.
induction n.
simpl (Zpower 2 0).
intros.
apply Zpower_1.
intros.
destruct m.
inversion H.
do 2 rewrite Zpower_S.
assert (n<=m)%nat.
omega.
generalize (IHn _ H0); intro.
omega.
Qed.

Lemma Zpower_2_lt : forall n m,
  (n < m)%nat ->
  Zpower 2 n < Zpower 2 m.
induction n.
simpl (Zpower 2 0).
intros.
destruct m.
inversion H.
rewrite Zpower_S.
generalize (Zpower_1 m); intros.
omega.
intros.
destruct m.
inversion H.
do 2 rewrite Zpower_S.
assert (n<m)%nat.
omega.
generalize (IHn _ H0); intro.
omega.
Qed.

Lemma Zpower_plus : forall n,
  Zpower 2 n + Zpower 2 n = Zpower 2 (S n).
  intros.
  rewrite Zpower_S.
  ring.
Qed.

Lemma Zpower_power : forall e,
  Zpower 2 e = Z_of_nat (power 2 e).
  induction e.
  simpl.
  reflexivity.
  rewrite Zpower_S.
  rewrite power_S.
  rewrite inj_mult.
  rewrite IHe.
  auto.
Qed.

Lemma Zeven_2 : forall m,
  Zeven (2*m).
  induction m; simpl; auto.
Qed.

Lemma Zpower_even : forall m,
  Zeven (Zpower 2 (S m)).
  induction m.
  simpl.
  apply I.
  rewrite Zpower_S.
  generalize (Zeven_div2 _ IHm); intros.
  rewrite H.
  apply Zeven_2.
Qed.

(*
 * Zbeta
 *)

Definition Zbeta (e:nat) := Zpower 2 (e * 32).

Lemma Zbeta_power1 : Zbeta 1 = Zpower 2 32.
  auto.
Qed.

Lemma Zpower_64_Zbeta : Zpower 2 64 = Zbeta 2.
  unfold Zbeta.
  simpl (2*32).
  reflexivity.
Qed.

Lemma Zbeta_is_exp : forall n m,
  Zbeta (n + m) = Zbeta n * Zbeta m.
  unfold Zbeta.
  intros.
  assert ((n + m) * 32 = n * 32 + m * 32)%nat.
  omega.
  rewrite H; clear H.
  rewrite Zpower_is_exp.
  auto.
Qed.

Lemma Zbeta_0 : forall l, 0 < Zbeta l.
  intros.
  unfold Zbeta.
  apply Zpower_0.
Qed.

Lemma Zbeta_1 : forall l, 1 <= Zbeta l.
  intros.
  unfold Zbeta.
  apply Zpower_1.
Qed.

Lemma Zbeta_lt : forall m n,
  (m < n)%nat ->
  Zbeta m < Zbeta n.
  intros.
  unfold Zbeta.
  apply Zpower_2_lt.
  omega.
Qed.

Lemma Zbeta_le : forall m n,
  (m <= n)%nat ->
  Zbeta m <= Zbeta n.
  intros.
  unfold Zbeta.
  apply Zpower_2_le.
  omega.
Qed.

Lemma Zpower_shift_2 : forall n,
  4*n < Zbeta 1 ->
  n < Zpower 2 30.
  intros.
  rewrite Zbeta_power1 in H.
  cutrewrite (32 = 2 + 30)%nat in H.
  rewrite Zpower_is_exp in H.
  simpl (Zpower 2 2) in H.
  omega.
  auto.
Qed.

Lemma Zbeta_power : forall (e:nat), Zbeta e = Zpower 2 (e * 32).
  auto.
Qed.

(*
 * equality modulo
 *)

Definition eqmod (a b m:Z) := exists k:Z,
  a = b + k * m.

Notation "a == b [[ m ]]" := (eqmod a b m) (at level 80).
  

(****************************************************************************)

Require Import Znumtheory.

Open Local Scope Z_scope.

Lemma Zis_gcd_eq : forall n m, 0 <= n -> 
  Zis_gcd n n m -> n = m \/ n = - m.
  intros.
  inversion H0.
  generalize (H3 n (Zdivide_refl n) (Zdivide_refl n)); intro.
  generalize (Zdivide_antisym _ _ H4 H1); intro.
  auto.
Qed.

Close Local Scope Z_scope.
