(*
 *  Seplog is an implementation of separation logic (an extension of Hoare
 *  logic by John C. Reynolds, Peter W. O'Hearn, and colleagues) in the
 *  Coq proof assistant (version 8, http://coq.inria.fr) together with a
 *  sample verification of the heap manager of the Topsy operating system
 *  (version 2, http://www.topsy.net). More information is available at
 *  http://web.yl.is.s.u-tokyo.ac.jp/~affeldt/seplog.
 *
 *  Copyright (c) 2005 Reynald Affeldt and Nicolas Marti
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

(* the fields of the cell structure *)

Definition data := 0%Z.
Definition next := 1%Z.

(* a tactic unfolding fields name to their offset *)
Ltac Unfolds_fields := unfold data; unfold next.

(* the reverse list algorithm *)
Definition reverse_list (i j k:var.v) :=
  j <- nat_e 0;
  while (var_e i =/= nat_e 0) (

       k <-* (i -.> next);
       (i -.> next) *<- var_e j;
       j <- var_e i;
       i <- var_e k

    ).

(* this assertion represents the fact that a list begin at an adress *)
Inductive list_assert : list Z -> nat -> nat ->  store.s -> heap.h -> Prop :=
     list_end : forall i j l s h,
                      sep.emp s h ->
                      i = j ->
                      l = nil ->
                      list_assert l i j s h
    | list_suiv: forall l l' d i j k s h h1 h2,
                      h1 # h2 ->
                      h = (h1 +++ h2) ->
                      i <> k ->
                      i <> j ->
                      l = d::l' ->
                      (nat_e i |--> int_e d::nat_e j::nil) s h1 ->
                      (list_assert l' j k) s h2 ->
                      list_assert l i k s h.

Definition list_empty : list Z := nil.

(* A list reversion of coq list *)
Fixpoint list_reverse_coq (l:list Z) : list Z :=
   match l with
     nil => nil
     | a :: l' => list_reverse_coq l' ++ a::nil 
   end.

Eval compute in (list_reverse_coq (3::6::8::1::8::9::13::nil)%Z).

Lemma list_reverse_coq_lemma1: forall l a,
  list_reverse_coq (l ++ a::nil) = a::list_reverse_coq l.
induction l; auto.
intros.
simpl.
rewrite IHl; auto.
Qed.

Lemma list_reverse_coq_lemma2: forall l,
  list_reverse_coq (list_reverse_coq l) = l.
  induction l; auto.
  simpl.
  rewrite list_reverse_coq_lemma1.
  rewrite IHl; auto.
Qed.

Lemma list_assert_inde_store: forall l i j s1 s2 h,
  list_assert l i j s1 h -> list_assert l i j s2 h.
  intros.
  induction H.
  apply list_end; auto.
  eapply list_suiv with (h1 := h1) (h2 := h2) (d := d) (j := j).
  auto.
  auto.
  auto.
  intuition.
  apply H3.
  auto.
  auto.
Qed.

(* precondition and postcondition of reverse_list *)
Definition reverse_precondition (l: list Z) (hd: var.v) : assert := 
  fun s h => exists v, eval (var_e hd) s = Z_of_nat v /\ (list_assert l v 0) s h.

Definition reverse_postcondition (l: list Z) (hd: var.v) : assert := 
  fun s h => exists v, eval (var_e hd) s = Z_of_nat v /\ (list_assert (list_reverse_coq l) v 0) s h.

(* reverse_list specification *)
Definition reverse_list_specif: Prop := forall l i j k,
  var.set (i::j::k::nil) ->
    {{reverse_precondition l i}}
    reverse_list i j k
    {{reverse_postcondition l j}}.

Lemma list_assert_hd_uneq: forall l1 l2 hd1 hd2 s h,
   (list_assert l1 hd1 0 ** list_assert l2 hd2 0) s h -> hd1 <> 0 ->
   hd1 <> hd2.
intros.
Decompose_sepcon H h1 h2.
inversion_clear H1.
intuition.
inversion_clear H4.
intuition.
simpl in H9.
Decompose_sepcon H9 h31 h32.
simpl in H15.
Decompose_sepcon H15 h51 h52.
red in H18.
red in H9.
inversion_clear H9.
inversion_clear H21.
inversion_clear H18.
inversion_clear H21.
simpl in H9.
rewrite Z_of_nat2loc in H9.
simpl in H18.
rewrite Z_of_nat2loc in H18.
injection H9; injection H18; intros.
subst x0 x.
simpl in H24; simpl in H23.
eapply heap.disjoint_singleton' with (z := d) (z' := d0).
rewrite <-H24.
eapply heap.disjoint_com.
rewrite <-H23.
Disjoint_heap.
Qed.

Ltac Decompose_inverse_list_hyp := red; intros; Decompose_hyp.

Ltac Resolve_inverse_list_goal := 
  match goal with
    | |- ?P1 /\ ?P2 => split; [Resolve_inverse_list_goal | Resolve_inverse_list_goal]
    | id: list_assert ?l ?st ?ed ?s1 ?h1 |- list_assert ?l ?st ?ed ?s2 ?h2 => assert (A1: h2 = h1); [Heap_emp_clean; Equal_heap | rewrite A1; clear A1; eapply (list_assert_inde_store); apply id] 
    | id: list_assert ?l ?st ?ed ?s1 ?h |- list_assert ?l ?st ?ed ?s2 ?h => eapply (list_assert_inde_store); apply id
    | |- update_store2 ?x ?v ?P => red; Resolve_inverse_list_goal
    | |- _ => (Store_update || auto)
    | _ => idtac
  end.

Ltac Resolve_inverse_list:= Decompose_inverse_list_hyp; Resolve_inverse_list_goal.

(* reverse_list verification *)
Lemma reverse_list_verif: reverse_list_specif.
unfold reverse_list_specif.
intros.
unfold reverse_list.
unfold reverse_precondition.
unfold reverse_postcondition.

eapply semax_assign'' with (fun s h => exists v, 
   store.lookup i s = Z_of_nat v /\ 
   (list_assert l v 0) s h /\
   store.lookup j s = Z_of_nat 0
).

Resolve_inverse_list.
red.
exists x.
Resolve_inverse_list_goal.

apply semax_while' with (fun s h => exists l1, exists l2,
    l = l1 ++ l2 /\
    exists v_i, exists v_j,
        store.lookup i s = Z_of_nat v_i /\
        store.lookup j s = Z_of_nat v_j /\
        (list_assert l2 v_i 0 ** list_assert (list_reverse_coq l1) v_j 0) s h
).

Resolve_inverse_list.
exists list_empty; exists l.
Resolve_inverse_list_goal.
exists x; exists 0.
Resolve_inverse_list_goal.
unfold list_empty; simpl.
Compose_sepcon h heap.emp; [Resolve_inverse_list_goal | idtac].
eapply list_end; [red; auto | auto | auto].

apply semax_strengthen_pre with (fun s h =>
exists l1, exists l2, exists elt,
    l = l1 ++ (elt::l2) /\
    exists v_i, exists v_j,
        store.lookup i s = Z_of_nat v_i /\
        store.lookup j s = Z_of_nat v_j /\
        v_i <> 0 /\ 
        v_i <> v_j /\
        ((list_assert (elt::l2) v_i 0) ** (list_assert (list_reverse_coq l1) v_j 0)) s h
).

Resolve_inverse_list.
inversion_clear H7.
assert (x1 <> 0).
intro; subst x1; OmegaZ.
contradiction.
subst x0.
exists x; exists l'; exists d.
split; auto.
exists x1; exists x2.
assert ((list_assert (d :: l') x1 0 ** list_assert (list_reverse_coq x) x2 0) s h).
Compose_sepcon H3 H4; [idtac | apply H10].
eapply list_suiv with (h1 := h1) (h2 := h2).
Disjoint_heap.
Equal_heap.
OmegaZ.
apply H13.
intuition.
auto.
auto.
Resolve_inverse_list_goal.
eapply list_assert_hd_uneq with (h := h) (l1 := d::l'); [idtac | OmegaZ].
apply H7.

apply semax_lookup_backwards'' with (fun s h =>
exists l1, exists l2, exists elt,
    l = l1 ++ (elt::l2) /\
    exists v_i, exists v_j, exists v_k,
        store.lookup i s = Z_of_nat v_i /\
        store.lookup j s = Z_of_nat v_j /\
        store.lookup k s = Z_of_nat v_k /\
        v_i <> 0 /\ 
        v_i <> v_j /\ 
        (list_assert (elt::nil) v_i v_k ** (list_assert l2 v_k  0) ** (list_assert (list_reverse_coq l1) v_j 0)) s h
).

Resolve_inverse_list.
inversion_clear H8.
inversion H13.
simpl in H16.
Decompose_hyp.
unfold next.
exists (nat_e j0).
Compose_sepcon H21 (H8 +++ h2 +++ H6).
Mapsto.
rewrite H1; OmegaZ.
Intro_sepimp H21' h'.
red.
injection H15; intros.
subst x0 x1.
clear H15.
exists x; exists l'; exists d.
Resolve_inverse_list_goal.
exists x2; exists x3; exists j0.
Resolve_inverse_list_goal.
Compose_sepcon (h2 +++ H8 +++ H21') H6.
Compose_sepcon (H8 +++ H21') h2.
eapply list_assert_inde_store with s.
eapply list_suiv with (h1 := H8 +++ H21') (h2 := heap.emp).
Disjoint_heap.
Equal_heap.
auto.
apply H14.
intuition.
simpl.
Compose_sepcon H8 H21'.
Mapsto.
Compose_sepcon H21' heap.emp.
Mapsto.
rewrite H1.
OmegaZ.
red; auto.
apply list_end.
red; auto.
auto.
auto.
Resolve_inverse_list_goal.
Resolve_inverse_list_goal.

apply semax_mutation_backwards'' with (fun s h =>
exists l1, exists l2, exists elt,
    l = l1 ++ (elt::l2) /\
    exists v_i, exists v_k,
        store.lookup i s = Z_of_nat v_i /\
        store.lookup k s = Z_of_nat v_k /\
        v_i <> 0 /\ 
        (list_assert (list_reverse_coq (l1 ++ elt ::nil)) v_i 0 ** (list_assert l2 v_k  0)) s h
).

Resolve_inverse_list.
unfold next.
inversion_clear H14.
inversion H19.
injection H21; intros; subst d l'; clear H21.
inversion_clear H23; [idtac | inversion H26].
subst j0; clear H24; clear H20.
simpl in H22.
Decompose_hyp.
exists (nat_e x4).
Compose_sepcon H25 (H20 +++ H9 +++  H7).
Mapsto.
rewrite H2; OmegaZ.
Intro_sepimp H25' h'.
exists x; exists x0; exists x1.
split; auto.
exists x2; exists x4.
Resolve_inverse_list_goal.
Compose_sepcon (H20 +++ H25' +++ H7) H9.
rewrite list_reverse_coq_lemma1.
eapply list_suiv with (h1 := (H20 +++ H25')) (h2 := H7).
Disjoint_heap.
Equal_heap.
OmegaZ.
apply H6.
intuition.
simpl.
Compose_sepcon H20 H25'.
Mapsto.
Compose_sepcon H25' heap.emp.
Mapsto.
rewrite H2; OmegaZ.
red; auto.
auto.
auto.

apply semax_assign'' with (fun s h =>
exists l1, exists l2, exists elt,
    l = l1 ++ (elt::l2) /\
    exists v_j, exists v_k,
        store.lookup j s = Z_of_nat v_j /\
        store.lookup k s = Z_of_nat v_k /\
        ((list_assert (list_reverse_coq (l1 ++ elt ::nil)) v_j  0) ** (list_assert l2 v_k  0)) s h
).

Resolve_inverse_list.
red; simpl.
exists x; exists x0; exists x1.
split; auto.
exists x2; exists x3.
Resolve_inverse_list_goal.
Compose_sepcon H2 H5.
Resolve_inverse_list_goal.
Resolve_inverse_list_goal.

apply semax_assign'.

Resolve_inverse_list.
red; simpl.
exists (x ++ x1::nil); exists x0.
split.
rewrite app_ass; simpl; auto.
exists x3; exists x2.
Resolve_inverse_list_goal.
Compose_sepcon H3 H2.
Resolve_inverse_list_goal.
Resolve_inverse_list_goal.

Resolve_inverse_list.
assert (x1 = 0).
rewrite H1 in H2.
OmegaZ.
subst x1.
inversion_clear H7; [idtac | tauto].
subst x0.
rewrite <- app_nil_end in H0.
subst x.
exists x2.
Resolve_inverse_list_goal.
Qed.



