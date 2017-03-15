(*
 *  Seplog is an implementation of separation logic (an extension of Hoare
 *  logic by John C. Reynolds, Peter W. O'Hearn, and colleagues) in the
 *  Coq proof assistant (version 8, http://coq.inria.fr) together with a
 *  sample verification of the heap manager of the Topsy operating system
 *  (version 2, http://www.topsy.net). More information is available at
 *  http://web.yl.is.s.u-tokyo.ac.jp/~affeldt/seplog.
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

Load seplog_header.

Require Import topsy_hm.

(* 
a remettre dans bipl.v apres nettoyage
*)

Lemma eval_store_update: forall e x v s,
     eval e (store.update x v s) = eval (expr_rewrite e (var_e x) (int_e v)) s.
induction e.
simpl; intros.
generalize (beq_nat_classic v x); intro X; inversion_clear X.
generalize (beq_nat_true _ _ H); intros.
subst v.
rewrite H.
rewrite store_lookup_update'.
auto.
rewrite H.
generalize (beq_nat_false v x H); intros.
rewrite store_lookup_update.
auto.
auto.
auto.
simpl; intros.
rewrite IHe1; rewrite IHe2; auto.
simpl; intros.
rewrite IHe1; rewrite IHe2; auto.
simpl; intros.
rewrite IHe1; rewrite IHe2; auto.
simpl; intros.
rewrite IHe1; rewrite IHe2; auto.
Qed.

Lemma eval_b_store_update: forall b x v s,
     eval_b b (store.update x v s) = eval_b (expr_b_rewrite b (var_e x) (int_e v)) s.
induction b.
simpl; intros.
auto.
simpl; intros; repeat rewrite eval_store_update; auto.
simpl; intros; repeat rewrite eval_store_update; auto.
simpl; intros; repeat rewrite eval_store_update; auto.
simpl; intros; repeat rewrite eval_store_update; auto.
simpl; intros; rewrite IHb; auto.
simpl; intros; rewrite IHb1; rewrite IHb2; auto.
simpl; intros; rewrite IHb1; rewrite IHb2; auto.
Qed.

(***********************)


Inductive abstract_hl: list (loc * expr) -> loc -> nat -> store.s -> heap.h -> Prop :=
  abstract_hl_last: forall l start size s h,
      size = 0 ->
      l = nil ->
      sep.emp s h ->
      abstract_hl l start size s h
  | abstract_hl_free: forall l l' adr start size s h h1 h2,
      start = adr ->
      size > 0 ->
      l = (adr, Free)::l' ->
      h1 # h2 -> h = (h1 +++ h2) ->
      ((nat_e start) |-> Free) s h1 ->
      abstract_hl l' (start + 1) (size - 1) s h2 ->
      abstract_hl l start size s h
  | abstract_hl_alloc: forall l l' adr start size s h h1 h2,
      start = adr ->
      size > 0 ->
      l = (adr, Allocated)::l' ->
      h1 # h2 -> h = (h1 +++ h2) ->
      ((nat_e start) |-> Allocated) s h1 ->
      abstract_hl l' (start + 1) (size - 1) s h2 ->
      abstract_hl l start size s h.


Lemma abstract_hl_inde_store: forall l start size s s' h,
   abstract_hl l start size s h -> abstract_hl l start size s' h.
intros.
induction H.
eapply abstract_hl_last; [auto | auto | auto].
eapply abstract_hl_free; [apply H | auto | apply H1 | apply H2 | apply H3 | trivial | trivial].
eapply abstract_hl_alloc; [apply H | auto | apply H1 | apply H2 | apply H3 | trivial | trivial].
Qed.

Lemma abstract_hl_start: forall l a b start size s h,
   abstract_hl ((a,b)::l) start size s h -> a = start.
intros.
inversion_clear H.
inversion H1.
injection H2; intros; subst a start; auto.
injection H2; intros; subst a start; auto.
Qed.

Lemma abstract_hl_size: forall l start size s h,
   abstract_hl l start size s h -> size = length l.
induction l.
simpl.
intros.
inversion_clear H.
auto.
inversion H2.
inversion H2.
simpl.
intros.
inversion_clear H.
inversion H1.
injection H2; intros; subst l'.
generalize (IHl _ _ _ _ H6).
intros.
omega.
injection H2; intros; subst l'.
generalize (IHl _ _ _ _ H6).
intros.
omega.
Qed.

Lemma abstract_hl_free_alloc: forall l a b start size s h,
   abstract_hl l start size s h -> In (a,b) l ->
   b = Free \/ b =Allocated.
induction l.
intros.
simpl in H0; inversion H0.
intros.
destruct a.
simpl in H0.
inversion_clear H0.
inversion_clear H.
inversion H2.
injection H1; intros; subst l0 e.
inversion H3.
tauto.
injection H1; intros; subst l0 e.
inversion H3.
tauto.
inversion_clear H.
inversion H2.
eapply IHl.
injection H3; intros; subst l'.
apply H7.
apply H1.
eapply IHl.
injection H3; intros; subst l'.
apply H7.
apply H1.
Qed.

Lemma abstract_hl_app: forall l1 l2 start size s h,
   abstract_hl (l1 ++ l2) start size s h ->
   (abstract_hl l1 start (size - length l2) ** abstract_hl l2 (start + length l1) (size - length l1)) s h.
induction l1.
intros.
simpl in H.
Compose_sepcon heap.emp h.
apply abstract_hl_last.
generalize (abstract_hl_size _ _ _ _ _ H); intros.
omega.
auto.
red; auto.
simpl.
cutrewrite (start + 0 = start); [idtac | omega].
cutrewrite (size - 0 = size); [idtac | omega].
auto.
simpl; intros.
destruct a.
generalize (abstract_hl_size _ _ _ _ _ H); intros.
simpl in H0.
rewrite length_app in H0.
inversion_clear H.
inversion H2.
injection H3; intros; subst l e l'; clear H3.
generalize (IHl1 _ _ _ _ _ H7); intros.
Decompose_sepcon H h21 h22.
Compose_sepcon (h1 +++ h21) h22. 
eapply abstract_hl_free with (h1 := h1) (h2 := h21).
apply H1.
omega.
intuition.
Disjoint_heap.
auto.
auto.
cutrewrite (size - length l2 - 1 = size - 1 - length l2); [auto | omega].
cutrewrite (size - S (length l1) = size - 1 - length l1); [auto | omega].
cutrewrite (start + S (length l1) = start + 1 + length l1); [auto | omega].
injection H3; intros; subst l e l'; clear H3.
generalize (IHl1 _ _ _ _ _ H7); intros.
Decompose_sepcon H h21 h22.
Compose_sepcon (h1 +++ h21) h22. 
eapply abstract_hl_alloc with (h1 := h1) (h2 := h21).
apply H1.
omega.
intuition.
Disjoint_heap.
auto.
auto.
cutrewrite (size - length l2 - 1 = size - 1 - length l2); [auto | omega].
cutrewrite (size - S (length l1) = size - 1 - length l1); [auto | omega].
cutrewrite (start + S (length l1) = start + 1 + length l1); [auto | omega].
Qed.

Lemma abstract_hl_app': forall l1 l2 start size s h,
   (abstract_hl l1 start (size - length l2) ** abstract_hl l2 (start + length l1) (size - length l1)) s h ->
   abstract_hl (l1 ++ l2) start size s h.
induction l1.
simpl; intros.
Decompose_sepcon H h1 h2.
inversion_clear H0.
cutrewrite (start = start + 0).
cutrewrite (size = size - 0).
assert (h = h2).
Equal_heap.
rewrite H0.
auto.
omega.
trivial.
inversion H5.
inversion H5.
destruct a.
simpl.
intros.
Decompose_sepcon H h1 h2.
inversion_clear H0.
inversion H4.
injection H5; intros; subst l e l'.
eapply abstract_hl_free with (h1 := h3) (h2 := (h2 +++ h4)).
apply H2.
omega.
intuition.
Disjoint_heap.
Equal_heap.
auto.
eapply IHl1.
Compose_sepcon h4 h2.
cutrewrite (size - 1 - length l2 = size - length l2 - 1); [auto | omega].
cutrewrite (start + 1 + length l1 = start + S (length l1)); [idtac | omega].
cutrewrite (size - 1 - length l1 = size - S (length l1)); [idtac | omega].
auto.
injection H5; intros; subst l e l'.
eapply abstract_hl_alloc with (h1 := h3) (h2 := (h2 +++ h4)).
apply H2.
omega.
intuition.
Disjoint_heap.
Equal_heap.
auto.
eapply IHl1.
Compose_sepcon h4 h2.
cutrewrite (size - 1 - length l2 = size - length l2 - 1); [auto | omega].
cutrewrite (start + 1 + length l1 = start + S (length l1)); [idtac | omega].
cutrewrite (size - 1 - length l1 = size - S (length l1)); [idtac | omega].
auto.
Qed.



Lemma abstract_hl_cons: forall l a b start size s h,
   abstract_hl ((a,b)::l) start size s h ->
   ((nat_e a |-> b) ** abstract_hl l (start + 1) (size - 1)) s h.
intros.
inversion_clear H.
inversion H1.
injection H2; intros; subst a b l'.
Compose_sepcon h1 h2.
Mapsto.
auto.
injection H2; intros; subst a b l'.
Compose_sepcon h1 h2.
Mapsto.
auto.
Qed.

Lemma abstract_hl_cons': forall l a b start size s h,
   b = Free \/ b =Allocated ->   
   a = start ->
   size > 0 ->
   ((nat_e a |-> b) ** abstract_hl l (start + 1) (size - 1)) s h ->
   abstract_hl ((a,b)::l) start size s h.
intros.
inversion_clear H.
Decompose_sepcon H2 h1 h2.
eapply abstract_hl_free with (h1 := h1) (h2 := h2).
intuition.
auto.
rewrite H0; rewrite H3; intuition.
auto.
auto.
rewrite <- H3; Mapsto.
auto.
Decompose_sepcon H2 h1 h2.
eapply abstract_hl_alloc with (h1 := h1) (h2 := h2).
intuition.
auto.
rewrite H0; rewrite H3; intuition.
auto.
auto.
rewrite <- H3; Mapsto.
auto.
Qed.

Axiom coucou: False.
Ltac Coucou := generalize coucou; contradiction.

Lemma abstract_hl_cell_gt: forall l a b x y start size s h,
   abstract_hl ((x, y) :: l) start size s h ->
   In (a, b) l ->
   a > x.
induction l.
simpl.
contradiction.
destruct a.
simpl; intros.
inversion_clear H0.
injection H1; intros; subst l0 e; clear H1.
generalize (abstract_hl_cons _ _ _ _ _ _ _ H); intros.
Decompose_sepcon H0 h1 h2.
generalize (abstract_hl_start _ _ _ _ _ _ _ H4); intro.
generalize (abstract_hl_start _ _ _ _ _ _ _ H); intro.
omega.
assert (l0 > x).
generalize (abstract_hl_cons _ _ _ _ _ _ _ H); intros.
Decompose_sepcon H0 h1 h2.
generalize (abstract_hl_start _ _ _ _ _ _ _ H5); intro.
generalize (abstract_hl_start _ _ _ _ _ _ _ H); intro.
omega.
generalize (abstract_hl_cons _ _ _ _ _ _ _ H); intros.
Decompose_sepcon H2 h1 h2.
assert (a > l0).
eapply IHl.
apply H6.
apply H1.
omega.
Qed.

Lemma abstract_hl_notin_list: forall (l: list (nat * expr)) a b x y start size s h,
  abstract_hl l start size s h ->
  In (a,b) l ->
  In (x,y) l ->
  b <> y ->
  a <> x.
induction l.
simpl.
contradiction.
destruct a.
simpl; intros.
inversion_clear H0.
inversion_clear H1.
injection H3; injection H0.
intros.
subst b; subst y; tauto.
injection H3; intros; subst n e; clear H3.
generalize (abstract_hl_cell_gt _ _ _ _ _ _ _ _ _ H H0); intros.
omega.
inversion_clear H1.
injection H0; intros; subst n e; clear H0.
generalize (abstract_hl_cell_gt _ _ _ _ _ _ _ _ _ H H3); intros.
omega.
inversion_clear H.
inversion H4.
injection H5; intros; subst l'.
eapply IHl.
apply H9.
apply H3.
apply H0.
auto.
injection H5; intros; subst l'.
eapply IHl.
apply H9.
apply H3.
apply H0.
auto.
Qed.

Definition abstract_hmAlloc (start: loc) (size: nat) (result i j: var.v) : cmd :=
   i <- (nat_e 0);
   j <-* ((nat_e start) +e (var_e i));
   while (((nat_e size) >> (var_e i)) &&& ((var_e j) =/= (Free))) (

      i <- ((var_e i) +e (nat_e 1));
      ifte ((nat_e size) >> (var_e i)) thendo 
          j <-* ((nat_e start) +e (var_e i))
      elsedo
         skip
   );
   (ifte ((nat_e size) >> (var_e i)) thendo (((nat_e start) +e (var_e i)) *<- Allocated; result <- ((nat_e start) +e (var_e i))) elsedo (result <- (int_e (-1)%Z))).

Definition abstract_hmAlloc_specif1 := forall start size result i j x, 
  (var.set (result::i::j::nil)) -> 
  size > 0 ->

  {{fun s h => exists l,  
        abstract_hl l start size s h /\
        In (x,Allocated) l}}
  
  abstract_hmAlloc start size result i j
  
  {{ fun s h => 
    (exists l, exists y, 
      eval (var_e result) s = Z_of_nat (y) /\
      abstract_hl l start size s h /\ 
      In (x,Allocated) l /\ 
      In (y,Allocated) l /\ 
      x <> y)

    \/

    (exists l, 
      eval (var_e result) s = (-1)%Z /\ 
      abstract_hl l start size s h /\ 
      In (x,Allocated) l) }}.




Lemma abstract_hmAlloc_verif1: abstract_hmAlloc_specif1.
unfold abstract_hmAlloc_specif1.
unfold abstract_hmAlloc.
intros.
Step (
fun (s : store.s) (h : heap.h) =>
     exists l : list (loc * expr),
       abstract_hl l start size s h /\ In (x, Allocated) l /\
       eval_b ((var_e i) ==  (nat_e 0)) s = true /\
       eval_b ((nat_e size) >> (var_e i)) s = true
).
inversion_clear H1 as [l].
inversion_clear H2.
unfold update_store2.
exists l.
split.
eapply abstract_hl_inde_store; apply H1.
split; auto.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite <- (beq_nat_refl i).
Omega_exprb.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite <- (beq_nat_refl i).
Omega_exprb.

Step (
fun (s : store.s) (h : heap.h) =>
     exists l : list (loc * expr), exists a, exists b,
       abstract_hl ((a,b)::l) start size s h /\ In (x, Allocated) ((a,b)::l) /\
       eval_b ((var_e i) ==  (nat_e 0)) s = true /\
       eval_b ((nat_e size) >> (var_e i)) s = true /\
       eval_b ((var_e j) == b) s = true
).
inversion_clear H1 as [l].
decompose [and] H2; clear H2.
destruct l.
simpl in H4; contradiction.
destruct p.
inversion H1.
inversion H5.

exists Free.
Compose_sepcon h1 h2.
Mapsto.
Intro_sepimp h1' h'.
assert (h1 = h1').
eapply singleton_equal.
apply H10.
apply H18.
Omega_exprb.
Omega_exprb.
assert (h = h').
Equal_heap.
rewrite <- H21.
unfold update_store2.
exists l.
exists l0; exists e.
split.
eapply abstract_hl_inde_store; apply H1.
split; auto.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite (beq_dif_false i j).
Omega_exprb.
Var_uneq.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite (beq_dif_false i j).
Omega_exprb.
Var_uneq.
injection H7.
intros; subst e; unfold Free.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite <- (beq_nat_refl).
Omega_exprb.

exists Allocated.
Compose_sepcon h1 h2.
Mapsto.
Intro_sepimp h1' h'.
assert (h1 = h1').
eapply singleton_equal.
apply H10.
apply H18.
Omega_exprb.
Omega_exprb.
assert (h = h').
Equal_heap.
rewrite <- H21.
unfold update_store2.
exists l.
exists l0; exists e.
split.
eapply abstract_hl_inde_store; apply H1.
split; auto.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite (beq_dif_false i j).
Omega_exprb.
Var_uneq.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite (beq_dif_false i j).
Omega_exprb.
Var_uneq.
injection H7.
intros; subst e; unfold Free.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite <- (beq_nat_refl).
Omega_exprb.

Step (
fun (s : store.s) (h : heap.h) =>
     exists l : list (loc * expr), exists a, exists b, exists l',
       abstract_hl (l++(a,b)::l') start size s h /\ In (x, Allocated) (l++(a,b)::l') /\
       eval_b ((var_e i) >>= (nat_e 0)) s = true /\
       (( eval_b (((var_e i) +e (nat_e start)) ==  (nat_e a)) s = true /\
          eval_b ((nat_e size) >> (var_e i)) s = true /\
          eval_b ((var_e j) == b) s = true /\
          b = Free) \/
        ( eval_b (((var_e i) +e (nat_e start)) ==  (nat_e a)) s = true /\
          eval_b ((nat_e size) >> (var_e i)) s = true /\
          eval_b ((var_e j) == b) s = true /\
          b = Allocated) \/
        (eval_b ((nat_e size) >> (var_e i)) s = false)
       )
).
inversion_clear H1 as [l].
inversion_clear H2 as [a].
inversion_clear H1 as [b].
decompose [and] H2; clear H2.
exists (@nil (prod loc expr)); exists a; exists b; exists l.
split; auto.
split.
auto.
assert (b = Free \/ b = Allocated).
eapply abstract_hl_free_alloc.
apply H1.
simpl; left; intuition.
assert (a=start).
eapply abstract_hl_start.
apply H1.
subst a.
split.
Omega_exprb.
inversion_clear H2.
subst b.
left.
split.
Omega_exprb.
split.
Omega_exprb.
split.
Omega_exprb.
auto.
subst b.
right; left.
split.
Omega_exprb.
split.
Omega_exprb.
split.
Omega_exprb.
auto.

Step (
fun (s : store.s) (h : heap.h) =>
     exists l : list (loc * expr), exists a, exists b, exists l',
       abstract_hl (l++(a,b)::l') start size s h /\ In (x, Allocated) (l++(a,b)::l') /\
       eval_b ((var_e i) >>= (nat_e 0)) s = true /\
       (( eval_b (((var_e i) +e (nat_e start)) ==  ((nat_e a) +e (nat_e 1))) s = true /\
          eval_b (((nat_e size) >> (var_e i)) ||| ((nat_e size) == (var_e i))) s = true /\
          eval_b ((var_e j) == b) s = true /\
          b = Allocated)    
       )
).
inversion_clear H1.
inversion_clear H2 as [l].
inversion_clear H1 as [a].
inversion_clear H2 as [b].
inversion_clear H1 as [l'].
decompose [and] H2; clear H2.
inversion_clear H7.
decompose [and] H2; clear H2.
subst b.
Omega_exprb.
inversion_clear H2.
decompose [and] H6; clear H6.
unfold update_store2.
exists l; exists a; exists b; exists l'.
split.
eapply abstract_hl_inde_store; apply H1.
split; auto.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite <- (beq_nat_refl).
Omega_exprb.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite <- (beq_nat_refl).
Omega_exprb.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite <- (beq_nat_refl).
Omega_exprb.
split.
subst b.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite (beq_dif_false j i).
Omega_exprb.
Var_uneq.
auto.
Omega_exprb.

Step TT.

Step TT.

red; intros.
inversion_clear H1.
inversion_clear H2 as [l].
inversion_clear H1 as [a].
inversion_clear H2 as [b].
inversion_clear H1 as [l'].
decompose [and] H2; clear H2.
destruct l'.
generalize (abstract_hl_app _ _ _ _ _ _  H1); intros.
Decompose_sepcon H2 h1 h2.
generalize (abstract_hl_start _ _ _ _ _ _ _ H13); intros.
generalize (abstract_hl_size _ _ _ _ _ H13); intros.
simpl in H14.
assert (eval_b (nat_e size == var_e i) s = true).
Omega_exprb.
assert (eval_b (nat_e size =/= var_e i) s = true).
Omega_exprb.
Omega_exprb.

destruct p.
generalize (abstract_hl_app _ _ _ _ _ _ H1); intros.
Decompose_sepcon H2 h1 h2.
generalize (abstract_hl_cons _ _ _ _ _ _ _ H13); intros.
Decompose_sepcon H12 h21 h22.
generalize (abstract_hl_cons _ _ _ _ _ _ _ H17); intros.
Decompose_sepcon H16 h221 h222.
generalize (abstract_hl_start _ _ _ _ _ _ _ H13); intros.
generalize (abstract_hl_start _ _ _ _ _ _ _ H17); intros.
exists e.
Compose_sepcon h221 (h222 +++ h21 +++ h1).
Mapsto.
Intro_sepimp h221' h'.
assert (h221' = h221).
eapply singleton_equal.
apply H24.
apply H18.
Omega_exprb.
Omega_exprb.
assert (h' = h).
rewrite H26 in H25.
clear H26.
Equal_heap.
rewrite H27.
unfold update_store2.
clear H27 H26 H25.
exists (l ++ (a,b)::nil); exists l0; exists e; exists l'.
split.
repeat rewrite app_ass.
simpl.
eapply abstract_hl_inde_store; apply H1.
split.
repeat rewrite app_ass.
simpl.
auto.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite (beq_dif_false i j).
Omega_exprb.
Var_uneq.
assert (e = Free \/ e = Allocated).
eapply abstract_hl_free_alloc.
apply H17.
simpl; left; intuition.
inversion_clear H25.

left.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite (beq_dif_false i j).
Omega_exprb.
Var_uneq.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite (beq_dif_false i j).
Omega_exprb.
Var_uneq.
split.
subst e.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite <- (beq_nat_refl).
Omega_exprb.
auto.

right; left.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite (beq_dif_false i j).
Omega_exprb.
Var_uneq.
split.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite (beq_dif_false i j).
Omega_exprb.
Var_uneq.
split.
subst e.
rewrite eval_b_store_update.
simpl expr_b_rewrite.
rewrite <- (beq_nat_refl).
Omega_exprb.
auto.

Step TT.
red; intros.
inversion_clear H1.
inversion_clear H2 as [l].
inversion_clear H1 as [a].
inversion_clear H2 as [b].
inversion_clear H1 as [l'].
decompose [and] H2; clear H2.
exists l; exists a; exists b; exists l'.
split.
auto.
split; auto.

Step TT.

eapply semax_strengthen_pre with (

fun (s : store.s) (h : heap.h) =>
     ((exists l : list (loc * expr),
         (exists a : loc,
            (exists b : expr,
               (exists l' : list (loc * expr),
                  abstract_hl (l ++ (a, b) :: l') start size s h /\
                  In (x, Allocated) (l ++ (a, b) :: l') /\
                  a <> x /\
                  eval_b (var_e i >>= nat_e 0) s = true /\
                  (eval_b ((var_e i +e nat_e start) == nat_e a) s = true /\
                   eval_b (nat_e size >> var_e i) s = true /\
                   eval_b (var_e j == b) s = true /\ b = Free ))))) /\
                   eval_b ((nat_e size >> var_e i) &&& (var_e j =/= Free)) s = false) /\
                   eval_b (nat_e size >> var_e i) s = true

).
red; intros.
decompose [and] H1; clear H1.
inversion_clear H4 as [l].
inversion_clear H1 as [a].
inversion_clear H2 as [b].
inversion_clear H1 as [l'].
decompose [and] H2; clear H2.
inversion_clear H8.
decompose [and] H2; clear H2.
split; try Omega_exprb.
split; try Omega_exprb.
exists l; exists a; exists b; exists l'.
split; auto.
split; auto.
split.
Coucou.
split; auto.
inversion_clear H2.
decompose [and] H7; clear H7.
subst b.
assert (eval_b (Free =/= Allocated) s = true).
unfold Free; unfold Allocated.
Omega_exprb.
assert (eval_b (Free == Allocated) s = true).
Omega_exprb.
Omega_exprb.
Omega_exprb.

Step (

fun (s : store.s) (h : heap.h) =>
     ((exists l : list (loc * expr),
         (exists a : loc,
            (exists b : expr,
               (exists l' : list (loc * expr),
                  abstract_hl (l ++ (a, b) :: l') start size s h /\
                  In (x, Allocated) (l ++ (a, b) :: l') /\
                  x <> a /\
                  eval_b (var_e i >>= nat_e 0) s = true /\
                  (eval_b ((var_e i +e nat_e start) == nat_e a) s = true /\
                   eval_b (nat_e size >> var_e i) s = true /\
                   b = Allocated ))))) /\
                   eval_b ((nat_e size >> var_e i) &&& (var_e j =/= Free)) s = false) /\
                   eval_b (nat_e size >> var_e i) s = true

).
inversion_clear H1.
inversion_clear H2.
inversion_clear H1 as [l].
inversion_clear H2 as [a].
inversion_clear H1 as [b].
inversion_clear H2 as [l'].
decompose [and] H1; clear H1.
generalize (abstract_hl_app _ _ _ _ _ _ H2); intros.
Decompose_sepcon H1 h1 h2.
generalize (abstract_hl_cons _ _ _ _ _ _ _ H15); intros.
Decompose_sepcon H14 h21 h22.
exists b.
Compose_sepcon h21 (h1 +++ h22).
Mapsto.
Intro_sepimp h21' h'.
split.
split.
exists l; exists a; exists Allocated; exists l'.
split.
apply abstract_hl_app'.
Compose_sepcon h1 (h22 +++ h21').
auto.
apply abstract_hl_cons'.
right; auto.
eapply abstract_hl_start.
apply H15.
generalize  (abstract_hl_size _ _ _ _ _  H2).
intros.
rewrite length_app in H22; simpl in H22.
omega.
Compose_sepcon h21' h22.
Mapsto.
auto.
split.
generalize (in_app_or _ _ _ H6) ; intro X; inversion_clear X.
apply in_or_app.
auto.
simpl in H22; inversion_clear H22.
injection H23; intro; contradiction.
apply in_or_app.
right; simpl; auto.
split; auto.
Omega_exprb.
Omega_exprb.

Step TT.
red; intros.
decompose [and] H1; clear H1.
inversion_clear H4 as [l]. 
inversion_clear H1 as [a].
inversion_clear H2 as [b].
inversion_clear H1 as [l'].
decompose [and] H2; clear H2.
(*red.*)
left.
exists (l++(a,b)::l').
exists a.
split.
Store_update.
split.
eapply abstract_hl_inde_store.
apply H1.
split; auto.
split; auto.
subst b.
apply in_or_app.
right; simpl; auto.

Step TT.
red; intros.
decompose [and] H1; clear H1.
inversion_clear H4 as [l].
inversion_clear H1 as [a].
inversion_clear H2 as [b].
inversion_clear H1 as [l'].
decompose [and] H2; clear H2.
(*red.*)
inversion_clear H8.
decompose [and] H2; clear H2.
subst b.
Omega_exprb.
inversion_clear H2.
decompose [and] H7; clear H7.
Omega_exprb.
right.
exists (l++(a,b)::l').
split.
Store_update.
split.
eapply abstract_hl_inde_store.
apply H1.
auto.
Qed.

