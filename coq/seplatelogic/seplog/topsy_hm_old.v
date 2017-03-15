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
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *)

Load seplog_header.

Open Local Scope Z_scope.

Definition HM_FREEFAILED := int_e 0.
Definition HM_FREEOK := int_e 1.

Definition Allocated := int_e 0.
Definition Free := int_e 1.

Definition status := 0.
Definition next := 1.

Definition hmStart : var.v := 0%nat.
Definition hmEnd : var.v := 1%nat.

Close Local Scope Z_scope.

(* A desciption of the heap list and useful lemmas *)

Inductive Heap_List : list (loc * nat * expr) -> loc -> loc -> store.s -> heap.h -> Prop :=

  Heap_List_last: forall s next startl endl h, endl = 0 -> next = 0 -> startl > 0 ->
    (nat_e startl |--> Allocated::nat_e next::nil) s h ->
    Heap_List nil startl endl s h

  | Heap_List_trans: forall s startl endl h, endl > 0 -> startl = endl ->  
    sep.emp s h ->
    Heap_List nil startl endl s h

  | Heap_List_suiv_Free: forall s h next startl endl h1 h2 hd_adr hd_size hd_expr tl ,
    h1 # h2 -> h = h1 +++ h2 ->
    hd_expr = Free ->
    next = startl + 2 + hd_size ->
    startl = hd_adr ->
    startl > 0 ->
    ((nat_e startl |--> hd_expr::nat_e next::nil) ** (Array (startl+2) hd_size)) s h1 ->
    Heap_List tl next endl s h2 ->
    Heap_List ((hd_adr, hd_size,hd_expr)::tl) startl endl s h

  | Heap_List_suiv_Allocated: forall s h next startl endl h1 h2 hd_adr hd_size hd_expr tl ,
    h1 # h2 -> h = h1 +++ h2 ->
    hd_expr = Allocated ->
    next = startl + 2 + hd_size ->
    startl = hd_adr ->
    startl > 0 ->
    (nat_e startl |--> hd_expr::nat_e next::nil) s h1 ->
    Heap_List tl next endl s h2 ->
    Heap_List ((hd_adr, hd_size,hd_expr)::tl) startl endl s h.

Definition hl_nil :  list (loc * nat * expr) := nil.

Lemma Heap_List_start_pos: forall l startl endl s h,
   (Heap_List l startl endl) s h ->
        startl > 0.
intros.
inversion_clear H.
auto.
subst endl.
auto.
auto.
auto.
Qed.

Lemma Heap_List_inde_store: forall l startl endl s h,
  Heap_List l startl endl s h -> forall s', Heap_List l startl endl s' h.
intros.
induction H.
eapply Heap_List_last.
auto.
apply H0.
auto.
trivial.
subst endl.
eapply Heap_List_trans.
trivial.
trivial.
trivial.
eapply Heap_List_suiv_Free.
apply H.
trivial.
trivial.
apply H2.
trivial.
trivial.
Decompose_sepcon H5 h11 h12.
Compose_sepcon h11 h12.
intuition.
subst hd_expr.
trivial.
subst hd_expr.
trivial.
eapply Array_inde_store; apply H10.
trivial.
eapply Heap_List_suiv_Allocated.
apply H.
trivial.
trivial.
apply H2.
trivial.
trivial.
Decompose_sepcon H5 h11 h12.
Compose_sepcon h11 h12.
intuition.
subst hd_expr.
trivial.
subst hd_expr.
trivial.
trivial.
Qed.

Ltac Heap_List_equiv := 
            match goal with
              | id: Heap_List ?l ?start1 ?end1 ?s1 ?h |-  Heap_List ?l ?start2 ?end2 ?s2 ?h =>
                  assert (Heap_List_equivA1: start2 = start1); [omega |
                     assert (Heap_List_equivA2: end2 = end1); [omega |
                        ((rewrite Heap_List_equivA1) || idtac); ((rewrite  Heap_List_equivA2) || idtac);
                        eapply (Heap_List_inde_store); apply id
                     ]
                  ]
            end.

Lemma Heap_List_equal_start: forall x sizex status startl endl l s h,
	Heap_List ((x,sizex,status)::l) startl endl s h ->	    
	startl = x.
intros.
inversion_clear H; [auto | auto].
Qed.

Lemma Heap_List_suiv_ge: forall l x sizex status a b c startl endl s h,
       	Heap_List ((a,b,c) ::l) startl endl s h ->
	In (x,sizex,status) l ->
	x > a.
induction l ; [simpl; contradiction | idtac].
simpl.
induction a.
induction a.
intros.
inversion_clear H0.
injection H1; intros; subst a b0 b; clear H1.
inversion_clear H.
inversion_clear H7.
omega.
omega.
inversion_clear H7.
omega.
omega.
inversion_clear H.
generalize  (IHl x sizex status0 a b0 b next0 endl s h2 H8 H1); intros.
generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H8); intro.
omega.
generalize  (IHl x sizex status0 a b0 b next0 endl s h2 H8 H1); intros.
generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H8); intro.
omega.
Qed.

Lemma Heap_List_block_adr_pos: forall l x sizex status startl endl s h,
       	Heap_List l startl endl s h ->
	In (x,sizex,status) l ->
	x > 0.
        induction l.
        simpl; intros; contradiction.
        clear IHl.
        induction a; induction a.
        intros.
        generalize (Heap_List_start_pos _ _ _ _ _ H); intros.
        generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H); intros.
        subst a.
        simpl in H0.
        inversion_clear H0.
        injection H2.
        intros; omega.
        generalize (Heap_List_suiv_ge _ _ _ _ _ _ _ _ _ _ _ H H2); intros.
        omega.
        Qed.





Lemma Heap_List_app : forall a b startl s h,
     startl > 0 ->
     (Heap_List (a ++ b) startl 0 s h 
     <-> 
     (exists j, ((Heap_List a startl j) ** (Heap_List b j 0)) s h)).
induction a.
split.
intros.
simpl in H0.
exists startl.
exists (heap.emp); exists h.
split.
Disjoint_heap.
split.
Equal_heap.
split.
apply Heap_List_trans.
auto.
auto.
red; auto.
auto.
intros.
simpl.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
decompose [and] H1; clear H1.
inversion_clear H2.
subst x.
inversion_clear H5.
inversion H8.
inversion H1.
inversion H11.
inversion H11.
subst x.
red in H6.
assert (A1: h = x1); [Heap_emp_clean; Equal_heap | rewrite A1; auto].

split.
intros.
simpl in H0.
inversion_clear H0.
subst startl.
assert (next0 > 0).
omega.

generalize (IHa b next0 s h2 H0); intro X; inversion_clear X.
generalize (H5 H8); intro; clear H0 H9 H5.
inversion_clear H10.
inversion_clear H0.
inversion_clear H5.
decompose [and] H0; clear H0.
exists x.
exists (heap.union h1 x0); exists x1.
split.
Disjoint_heap.
split.
Equal_heap.
split.
eapply Heap_List_suiv_Free with (h1 := h1) (h2:= x0).
Disjoint_heap.
Equal_heap.
auto.
apply H4.
auto.
auto.
auto.
auto.
auto.

subst startl.
assert (next0 > 0).
omega.
generalize (IHa b next0 s h2 H0); intro X; inversion_clear X.
generalize (H5 H8); intro; clear H0 H9 H5.
inversion_clear H10.
inversion_clear H0.
inversion_clear H5.
decompose [and] H0; clear H0.
exists x.
exists (heap.union h1 x0); exists x1.
split.
Disjoint_heap.
split.
Equal_heap.
split.
eapply Heap_List_suiv_Allocated with (h1 := h1) (h2:= x0).
Disjoint_heap.
Equal_heap.
auto.
apply H4.
auto.
auto.
auto.
auto.
auto.


intros.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
decompose [and] H1; clear H1.
simpl.
inversion_clear H2.
subst startl.
eapply Heap_List_suiv_Free with (h1 := h1) (h2 := (heap.union h2 x1)).
Disjoint_heap.
Equal_heap.
auto.
apply H7.
auto.
auto.
auto.
assert (next0 > 0).
omega.
generalize (IHa b next0 s (heap.union h2 x1) H2); intro X; inversion_clear X.
apply H12; clear H8 H12.
exists x.
exists h2; exists x1.
split.
Disjoint_heap.
split.
Equal_heap.
split.
auto.
auto.

intros.
simpl.
subst startl.
eapply Heap_List_suiv_Allocated with (h1 := h1) (h2 := (heap.union h2 x1)).
Disjoint_heap.
Equal_heap.
auto.
apply H7.
auto.
auto.
auto.
assert (next0 > 0).
omega.
generalize (IHa b next0 s (heap.union h2 x1) H2); intro X; inversion_clear X.
apply H12; clear H8 H12.
exists x.
exists h2; exists x1.
split.
Disjoint_heap.
split.
Equal_heap.
split.
auto.
auto.

Qed.

Ltac THeap_List_app_hyp id :=
              match goal with
                  | id : Heap_List (?l1 ++ ?l2) ?startl 0 ?s ?h |- _ =>
                             assert (THeap_List_app_H1: startl > 0); [apply (Heap_List_start_pos (l1 ++ l2) startl 0 s h id) | 
                             generalize (Heap_List_app l1 l2 startl s h THeap_List_app_H1); clear THeap_List_app_H1; intros THeap_List_app_H1; 
                             inversion_clear THeap_List_app_H1 as [THeap_List_app_H11 THeap_List_app_H12]; clear THeap_List_app_H12;
                             generalize (THeap_List_app_H11 id); clear THeap_List_app_H11; intro THeap_List_app_H1; 
                             inversion_clear THeap_List_app_H1
                             ]
              end.

Ltac THeap_List_app_goal:=
              match goal with
                  | |- Heap_List (?l1 ++ ?l2) ?startl 0 ?s ?h =>
                             assert (THeap_List_app_H1: startl > 0); [(omega || tauto) | 
                             generalize (Heap_List_app l1 l2 startl s h THeap_List_app_H1); clear THeap_List_app_H1; intros THeap_List_app_H1; 
                             inversion_clear THeap_List_app_H1 as [THeap_List_app_H11 THeap_List_app_H12]; clear THeap_List_app_H11;
                             eapply THeap_List_app_H12; clear THeap_List_app_H12
                             ]
              end.

Lemma Heap_List_block_status: forall l x sizex status startl s h,
        Heap_List l startl 0 s h ->
        In (x,sizex,status) l ->
        status = Allocated \/ status = Free.
intros.
generalize (list_split _ _ _ H0); intros.
inversion_clear H1 as [l1].
inversion_clear H2 as [l2].
subst l.
simpl in H.
THeap_List_app_hyp H; clear H.
Decompose_sepcon H1 h1 h2.
inversion_clear H4.
subst status0.
intuition.
subst status0.
intuition.
Qed.

Lemma Heap_List_block_status': forall l x sizex status startl endl s h,
        Heap_List l startl endl s h ->
        In (x,sizex,status) l ->
        status = Allocated \/ status = Free.
induction l.
intros.
inversion_clear H.
simpl in H0; tauto.
simpl in H0; tauto.
destruct a as [X st].
destruct X as [adr sz].
intros.
simpl in H0.
inversion_clear H0.
injection H1; intros; subst x sizex status0.
clear H1.
inversion_clear H.
right; auto.
left; auto.
inversion_clear H.
eapply IHl.
apply H8.
apply H1.
eapply IHl.
apply H8.
apply H1.
Qed.

Lemma Heap_List_app' : forall a b startl endl s h,
     startl > 0 ->
     endl > 0 ->
     (Heap_List (a ++ b) startl endl s h 
     <-> 
     (exists j, ((Heap_List a startl j) ** (Heap_List b j endl)) s h)).
induction a.
simpl.
intros.
split.
intros.
exists startl.
Compose_sepcon heap.emp h.
eapply Heap_List_trans.
auto.
auto.
red; auto.
auto.
intros.
inversion_clear H1.
Decompose_sepcon H2 h1 h2.
inversion H2.
subst x startl0 endl0 s0 h0.
inversion_clear H5.
inversion H10.
subst endl; inversion H0.
subst hd_adr.
inversion H13.
inversion_clear H13.
subst startl startl0 endl0 s0 h0.
red in H7.
assert (A1: h =h2); [Heap_emp_clean; Equal_heap | rewrite A1; auto].

simpl.
intros.
split.
intros.
inversion_clear H1.

subst hd_adr.
assert (next0 > 0).
subst next0; omega.
generalize (IHa b next0 endl s h2 H1 H0); intro X; inversion_clear X.
generalize (H6 H9); clear H6 H10.
intros.
inversion_clear H6.
Decompose_sepcon H10 h21 h22.
exists x.
Compose_sepcon (heap.union h21 h1) h22.
eapply Heap_List_suiv_Free with (h1 := h1) (h2 := h21).
Disjoint_heap.
Equal_heap.
auto.
apply H5.
auto.
auto.
auto.
auto.
auto.

subst hd_adr.
assert (next0 > 0).
subst next0; omega.
generalize (IHa b next0 endl s h2 H1 H0); intro X; inversion_clear X.
generalize (H6 H9); clear H6 H10.
intros.
inversion_clear H6.
Decompose_sepcon H10 h21 h22.
exists x.
Compose_sepcon (heap.union h21 h1) h22.
eapply Heap_List_suiv_Allocated with (h1 := h1) (h2 := h21).
Disjoint_heap.
Equal_heap.
auto.
apply H5.
auto.
auto.
auto.
auto.
auto.

intros.
inversion_clear H1.
Decompose_sepcon H2 h1 h2.
inversion_clear H2.

eapply Heap_List_suiv_Free with (h1 := h3) (h2 := (heap.union h4 h2)).
Disjoint_heap.
Equal_heap.
auto.
apply H8.
auto.
auto.
auto.
assert (next0 > 0).
subst next0; omega.
generalize (IHa b next0 endl s (heap.union h4 h2) H2 H0); intro X; inversion_clear X.
apply H14; clear H14 H13.
exists x.
Compose_sepcon h4 h2.
auto.
auto.

eapply Heap_List_suiv_Allocated with (h1 := h3) (h2 := (heap.union h4 h2)).
Disjoint_heap.
Equal_heap.
auto.
apply H8.
auto.
auto.
auto.
assert (next0 > 0).
subst next0; omega.
generalize (IHa b next0 endl s (heap.union h4 h2) H2 H0); intro X; inversion_clear X.
apply H14; clear H14 H13.
exists x.
Compose_sepcon h4 h2.
auto.
auto.
Qed.

Lemma Heap_List_last_bloc: forall adr size status l s h startl,
	Heap_List (l ++ ((adr,size,status)::nil)) startl 0 s h ->
	(Heap_List (l ++ ((adr,size,status)::nil)) startl (adr + 2 + size) ** Heap_List nil (adr + 2 + size) 0) s h.
   intros.
   generalize (Heap_List_start_pos _ _ _ _ _ H); intros.
   THeap_List_app_hyp H; clear H.
   Decompose_sepcon H1 h1 h2.
   inversion_clear H4.

   subst status0 next0 x.
   Compose_sepcon (h1 +++ h3) h4.
   assert (adr + 2 + size > 0).
   omega.
   generalize (Heap_List_app' l ((adr,size,Free)::nil) startl (adr + 2 + size) s (h1 +++ h3) H0 H4); intro X; inversion_clear X.
   apply H7.
   clear H6 H7.
   exists adr.
   Compose_sepcon h1 h3.
   auto.
   eapply Heap_List_suiv_Free with (h1 := h3) (h2 := heap.emp).
   Disjoint_heap.
   Equal_heap.
   auto.
   intuition.
   auto.
   auto.
   auto.
   eapply Heap_List_trans.
   omega.
   auto.
   red; auto.
   auto.

   subst status0 next0 x.
   Compose_sepcon (h1 +++ h3) h4.
   assert (adr + 2 + size > 0).
   omega.
   generalize (Heap_List_app' l ((adr,size,Allocated)::nil) startl (adr + 2 + size) s (h1 +++ h3) H0 H4); intro X; inversion_clear X.
   apply H7.
   clear H6 H7.
   exists adr.
   Compose_sepcon h1 h3.
   auto.
   eapply Heap_List_suiv_Allocated with (h1 := h3) (h2 := heap.emp).
   Disjoint_heap.
   Equal_heap.
   auto.
   intuition.
   auto.
   auto.
   auto.
   eapply Heap_List_trans.
   omega.
   auto.
   red; auto.
   auto.
Qed.

Lemma Heap_List_next_bloc: forall adr size status adr' size' status' l1 l2 s h startl,
	Heap_List (l1 ++ ((adr,size,status)::(adr',size',status')::nil) ++ l2) startl 0 s h ->
	adr' = (adr + 2 + size).
        intros.
        THeap_List_app_hyp H; clear H.
        Decompose_sepcon H0 h1 h2.
        generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H3); intros.
        subst x.
        inversion_clear H3.
        generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H10); intros.
        subst next0 adr'.
        auto.
        generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H10); intros.
        subst next0 adr'.
        auto.
Qed.


Lemma Compaction: forall l1 l2 x1 sizex1 sizex2 startl s h,
   startl > 0 ->
   (Heap_List (l1 ++ ((x1,sizex1,Free)::(x1 + 2 + sizex1,sizex2,Free)::nil) ++ l2) startl 0) s h ->
   (((nat_e x1 +e (int_e 1%Z))|->(nat_e (x1 + 2 + sizex1))) ** 
	 (((nat_e x1 +e (int_e 1%Z))|-> nat_e (x1 + sizex1 + 4 + sizex2)) -*
	        (Heap_List (l1 ++ ((x1, sizex1 + 2 + sizex2, Free)::nil) ++ l2 ) startl 0))) s h.

intros.
THeap_List_app_hyp H0.
Decompose_sepcon H1 h1 h2.
inversion_clear H5; [idtac | inversion H7].
subst next0 x1.
inversion_clear H12; [idtac | inversion H9].
subst next0.
clear H14 H7 H9.
simpl in H11.
Decompose_sepcon H11 h31 h32.
Decompose_sepcon H9 h311 h312.
Decompose_sepcon H19 h3121 h3122.
Compose_sepcon h3121 (h1 +++ h5 +++ h6 +++ h32 +++ h311).
auto.
Intro_sepimp h3121' h'.
THeap_List_app_goal.
exists x.
Compose_sepcon h1 (h3121' +++ h5 +++ h6 +++ h32 +++ h311).
auto.
simpl.
eapply Heap_List_suiv_Free with (h1 := h3121' +++ h5 +++  h32 +++ h311) (h2 := h6).
Disjoint_heap.
Equal_heap.
auto.
intuition.
auto.
auto.
Compose_sepcon (h3121' +++ h311) (h5 +++ h32).
simpl.
Compose_sepcon h311 h3121'.
auto.
Compose_sepcon h3121' heap.emp.
Mapsto.
red; auto.
TArray_concat_split_r sizex1 (2 + sizex2).
Compose_sepcon h32 h5.
auto.
TArray_concat_split_r  2 sizex2.
Decompose_sepcon H16 h51 h52.
Compose_sepcon h51 h52.
eapply mapstos_to_array.
apply H25.
simpl.
Omega_exprb.
simpl.
auto.
auto.
assert ((x + 2 + sizex1 + 2 + sizex2) = (x + 2 + (sizex1 + 2 + sizex2))).
Omega_exprb.
Heap_List_equiv.
Qed.

Lemma change_status_Free_to_Alloc: forall l1 l2 startl s h x sizex,
   startl > 0 -> 
   (Heap_List (l1 ++ ((x, sizex, Free)::nil) ++ l2) startl 0)  s h ->
   exists e,
   (((nat_e x) |-> e) **
   (((nat_e x) |-> Allocated) -* ((Heap_List (l1 ++ ((x, sizex, Allocated)::nil) ++ l2) startl 0) ** (Array (x+2) sizex)))) s h.
intros.
THeap_List_app_hyp H0.
Decompose_sepcon H1 h1 h2.
simpl in H5.
inversion_clear H5.
subst next0 x0.
simpl in H11.
Decompose_sepcon H11 h31 h32.
Decompose_sepcon H8 h311 h312.
Decompose_sepcon H16 h3121 h3122.
exists Free.
Compose_sepcon h311 (h312 +++ h32 +++ h4 +++ h1).
Mapsto.
Intro_sepimp h311' h'.
Compose_sepcon (h311' +++ h3121 +++ h1 +++ h4) h32.
THeap_List_app_goal.
exists x.
Compose_sepcon h1 (h311' +++ h3121 +++ h4).
auto.
simpl.
eapply Heap_List_suiv_Allocated with (h1 := h311' +++ h312) (h2 := h4).
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
intuition.
auto.
auto.
simpl.
Compose_sepcon h311' h312.
Mapsto.
Compose_sepcon h3121 heap.emp.
Mapsto.
red; auto.
auto.
auto.
inversion H7.
Qed.


Lemma change_status_Alloc_to_Free: forall l1 l2 startl s h x sizex,
   startl > 0 -> 
   ((Heap_List (l1 ++ ((x, sizex, Allocated)::nil) ++ l2) startl 0) ** (Array (x + 2) (sizex))) s h ->
   exists e,
   (((nat_e x) |-> e) **
   (((nat_e x) |-> Free) -* (Heap_List (l1 ++ ((x, sizex, Free)::nil) ++ l2) startl 0))) s h.
intros.
Decompose_sepcon H0 h1 h2.
THeap_List_app_hyp H1.
Decompose_sepcon H3 h11 h12.
simpl in H8.
inversion_clear H8.
inversion H10.
subst x0 next0.
simpl in H14.
Decompose_sepcon H14 h31 h32.
Decompose_sepcon H16 h321 h322.
red in H19.
exists Allocated.
Compose_sepcon h31 (h32 +++ h4 +++ h11 +++ h2).
Mapsto.
Intro_sepimp h31' h'.
THeap_List_app_goal.
exists x.
Compose_sepcon h11 (h31' +++ h32 +++ h4 +++ h2).
auto.
simpl.
eapply Heap_List_suiv_Free with (h1 := h31' +++ h32 +++ h2) (h2:= h4).
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
intuition.
auto.
auto.
simpl.
Compose_sepcon (h31' +++ h32) h2.
Compose_sepcon h31' h32.
Mapsto.
Compose_sepcon h321 heap.emp.
Mapsto.
red; auto.
auto.
auto.
Qed.


Lemma change_status_Free_to_Free: forall l1 l2 startl s h x sizex,
   startl > 0 -> 
   (Heap_List (l1 ++ ((x, sizex, Free)::nil) ++ l2) startl 0 s h) ->
   exists e,
   (((nat_e x) |-> e) **
   (((nat_e x) |-> Free) -* (Heap_List (l1 ++ ((x, sizex, Free)::nil) ++ l2) startl 0))) s h.
intros.
THeap_List_app_hyp H0.
Decompose_sepcon H1 h1 h2.
inversion_clear H5.
subst x0 next0.
simpl in H11.
Decompose_sepcon H11 h31 h32.
Decompose_sepcon H8 h311 h312.
Decompose_sepcon H16 h3121 h3122.
red in H19.
exists Free.
Compose_sepcon h311 (h312 +++ h32 +++ h4 +++ h1). 
Mapsto.
Intro_sepimp h311' h'.
simpl.
THeap_List_app_goal.
exists x.
Compose_sepcon h1 (h311' +++ h312 +++ h32 +++ h4).
auto.
eapply Heap_List_suiv_Free with (h1 := h311' +++ h312 +++ h32) (h2 := h4).
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
intuition.
auto.
auto.
simpl.
Compose_sepcon (h311' +++ h312) h32.
Compose_sepcon h311'  h312.
Mapsto.
Compose_sepcon h3121 heap.emp.
Mapsto.
red; auto.
Array_equiv.
Heap_List_equiv.
inversion H7.
Qed.



Lemma Splitting: forall l1 l2 x size1 size2 s h startl,
   startl > 0 ->
   Heap_List (l1 ++ ((x, size1 + 2 + size2, Free)::nil) ++ l2) startl 0 s h ->
   exists e'' : expr,
     (((nat_e (x + 3 + size1)) |-> e'') **
      (((nat_e (x + 3 + size1)) |-> (nat_e (x + 4 + size1 + size2))) -*
       (fun (s1 : store.s) (h1 : heap.h) =>
        exists e''0 : expr,
          (((nat_e (x + 2 + size1)) |-> e''0) **
           (((nat_e (x + 2 + size1)) |-> Free) -*
            (fun (s2 : store.s) (h2 : heap.h) =>
             exists e''1 : expr,
               (((nat_e (x + 1)) |-> e''1) **
                (((nat_e (x + 1)) |-> (nat_e (x + 2 + size1))) -*
                 (fun (s : store.s) (h : heap.h) =>
                  Heap_List (l1 ++ ((x, size1,Free)::(x + 2 + size1, size2,Free)::nil) ++ l2) startl 0 s h))) s2 h2))) s1 h1))) s h.
intros.
THeap_List_app_hyp H0.
Decompose_sepcon H1 h1 h2.
simpl in H5.
inversion_clear H5.
subst x0 next0.
Decompose_sepcon H11 h31 h32.
simpl in H8.
Decompose_sepcon H8 h311 h312.
Decompose_sepcon H16 h3121 h3122.
red in H19.
TArray_concat_split_l_l size1 H13.
Decompose_sepcon H18 h321 h322.
TArray_concat_split_l_l 2 H23.
Decompose_sepcon H22 h3221 h3222.
simpl in H24.
Decompose_sepcon H24 h32211 h32212.
inversion_clear H26.
Decompose_sepcon H30 h322121 h322122.
inversion_clear H30.
red in H33.
exists (int_e x1).
Compose_sepcon h322121 (h32211 +++ h3222 +++ h321 +++ h31 +++ h4 +++ h1).
Mapsto.
Intro_sepimp h322121' h'.
exists (int_e x0).
Compose_sepcon h32211 (h322121' +++ h3222 +++ h321 +++ h31 +++ h4 +++ h1).
Mapsto.
Intro_sepimp h32211' h''.
exists (nat_e (x + 2 + (size1 + 2 + size2))).
Compose_sepcon h3121 (h1 +++ h4 +++ h311 +++ h321 +++ h3222 +++ h32211' +++ h322121').
Mapsto.
Intro_sepimp h3121' h'''.
THeap_List_app_goal.
exists x.
Compose_sepcon h1 (h3121'  +++ h4 +++ h311 +++ h321 +++ h3222 +++ h32211' +++ h322121').
auto.
simpl.
eapply Heap_List_suiv_Free with (h1 := h311 +++ h3121' +++ h321) (h2 := h4 +++ h3222 +++ h32211' +++ h322121').
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
intuition.
auto.
auto.
simpl.
Compose_sepcon (h3121' +++ h311)  h321.
Compose_sepcon h311 h3121' .
Mapsto.
Compose_sepcon h3121' heap.emp; [Mapsto | red; auto].
auto.
eapply Heap_List_suiv_Free with (h1 := h3222 +++ h32211' +++ h322121') (h2 := h4).
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
intuition.
auto.
omega.
simpl.
Compose_sepcon (h32211' +++ h322121') h3222.
Compose_sepcon h32211' h322121'.
Mapsto.
Compose_sepcon h322121' heap.emp; [Mapsto | red; auto].
Array_equiv.
Heap_List_equiv.
inversion H7.
Qed.    

Lemma Heap_List_header: forall x sizex statusx startl endl l s h,
        Heap_List ((x, sizex, statusx)::l) startl endl s h ->
        x = startl /\
        (Heap_List ((x, sizex, statusx)::nil) x (x + 2 + sizex) ** Heap_List l (x + 2 + sizex) endl) s h.
intros.
inversion_clear H.
subst statusx startl next0.
split; auto.
Decompose_sepcon H6 h11 h12.
Compose_sepcon h1 h2.
eapply Heap_List_suiv_Free with (h1 := h1) (h2 := heap.emp).
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
auto.
auto.
auto.
Compose_sepcon h11 h12.
auto.
auto.
eapply Heap_List_trans.
omega.
intuition.
red; auto.
auto.
subst statusx startl next0.
split; auto.
Compose_sepcon h1 h2.
eapply Heap_List_suiv_Allocated with (h1 := h1) (h2 := heap.emp).
Disjoint_heap.
Heap_emp_clean; Equal_heap.
auto.
intuition.
auto.
auto.
auto.
eapply Heap_List_trans.
omega.
intuition.
red; auto.
auto.
Qed.


Ltac Heap_List_Trans := 
eapply Heap_List_trans; [auto | (Omega_exprb || auto) | red; Equal_heap].


Lemma Heap_List_next: forall l1 l2 bloc_adr bloc_size bloc_status startl s h e x P,
(Heap_List (l1 ++ ((bloc_adr, bloc_size, bloc_status) :: nil) ++ l2) startl 0 ** TT) s h ->
eval e s = eval (nat_e (bloc_adr + 1)) s ->
((update_store2 x (nat_e (bloc_adr + 2 +bloc_size)) P) s h) ->
exists e0, ((e |-> e0) ** ((e |-> e0)  -* update_store2 x e0 P)) s h.
intros.
eapply semax_lookup_simple with (nat_e (bloc_adr + 2 + bloc_size)).
Decompose_sepcon H h1 h2.
THeap_List_app_hyp H2; clear H2.
Decompose_sepcon H4 h11 h12.
inversion_clear H8.

subst x0 next0 bloc_status.
simpl in H14.
Decompose_sepcon H14 h31 h32.
Decompose_sepcon H10 h311 h312.
Decompose_sepcon H18 h3121 h3122.
Compose_sepcon h3121 (h3122 +++ h311 +++ h32 +++ h11 +++ h2 +++ h4).
Mapsto.
red; auto.

subst x0 next0 bloc_status.
simpl in H14.
Decompose_sepcon H14 h31 h32.
Decompose_sepcon H14 h321 h322.

Compose_sepcon h321 (h31 +++ h4 +++ h11 +++ h2).

Mapsto.
red; auto.

auto.
Qed.

Lemma Heap_List_next': forall l bloc_adr bloc_size bloc_status startl s h e x P,
In (bloc_adr, bloc_size, bloc_status) l ->
(Heap_List l startl 0 ** TT) s h ->
eval e s = eval (nat_e (bloc_adr + 1)) s ->
((update_store2 x (nat_e (bloc_adr + 2 +bloc_size)) P) s h) ->
exists e0, ((e |-> e0) ** ((e |-> e0)  -* update_store2 x e0 P)) s h.
intros.
generalize (list_split _ _ _ H); intro.
inversion_clear H3 as [l1].
inversion_clear H4 as [l2].
subst l.
eapply Heap_List_next.
Decompose_sepcon H0 h1 h2.
Compose_sepcon h1 h2.
apply H3.
red; auto.
auto.
auto.
Qed.

Lemma Heap_List_next_last: forall bloc_adr s h e x P,
bloc_adr > 0 -> 
(Heap_List nil bloc_adr 0 ** TT) s h ->
eval e s = eval (nat_e (bloc_adr + 1)) s ->
((update_store2 x (nat_e 0) P) s h) ->
exists e0, ((e |-> e0) ** ((e |-> e0)  -* update_store2 x e0 P)) s h.
intros.
eapply semax_lookup_simple with (nat_e 0).
Decompose_sepcon H0 h1 h2.
inversion_clear H3.
subst next0; clear H5.
simpl in H9.
Decompose_sepcon H9 h11 h12.
Decompose_sepcon H10 h121 h122.
Compose_sepcon h121 (h11 +++ h2).
Mapsto.
red; auto.
inversion H5.
auto.
Qed.

Lemma Heap_List_status: forall l adr size status e x P startl s h ,
In (adr,size,status) l ->
(Heap_List l startl 0 ** TT) s h ->
eval e s = eval (nat_e adr) s ->
(update_store2 x status P) s h ->
exists e0, ((e |-> e0) ** ((e |-> e0)  -* update_store2 x e0 P)) s h.
intros.
generalize (list_split _ _ _ H); intros.
inversion_clear H3 as [l1].
inversion_clear H4 as [l2].
subst l.
Decompose_sepcon H0 h1 h2.
THeap_List_app_hyp H2.
Decompose_sepcon H5 h11 h12.
inversion_clear H10.

subst status0 next0 x0.
eapply semax_lookup_simple with Free.
simpl in H16.
Decompose_sepcon H16 h31 h32.
Decompose_sepcon H12 h311 h312.
Compose_sepcon h311 (h312 +++ h32 +++ h4 +++ h11 +++ h2).
Mapsto.
red; auto.
auto.
subst status0 next0 x0.
simpl in H16.
Decompose_sepcon H16 h31 h32.
eapply semax_lookup_simple with Allocated.
Compose_sepcon h31 ( h32 +++ h4 +++ h11 +++ h2).
Mapsto.
red; auto.
auto.
Qed.


Lemma Heap_List_status_last: forall bloc_adr s h e x P,
bloc_adr > 0 -> 
(Heap_List nil bloc_adr 0 ** TT) s h ->
eval e s = eval (nat_e bloc_adr) s ->
(update_store2 x Allocated P) s h  ->
exists e0, ((e |-> e0) ** ((e |-> e0)  -* update_store2 x e0 P)) s h.
intros.
Decompose_sepcon H0 h1 h2.
inversion_clear H3.
exists Allocated.
subst next0; clear H5.
simpl in H9.
Decompose_sepcon H9 h11 h12.
Compose_sepcon h11 (h12 +++ h2).
Mapsto.
Intro_sepimp h'11 h'.
assert (h'11 = h11).
eapply singleton_equal.
apply H11.
apply H5.
Omega_exprb.
Omega_exprb.
subst h'11.
assert (h' = h).
Equal_heap.
rewrite H13.
auto.
inversion H5.
Qed.


Lemma Heap_List_bloc_unique: forall l startl s h adr size size' status status',
    Heap_List l startl 0 s h ->
    In (adr, size, status) l ->
    In (adr, size', status') l ->
    status = status' /\ size = size'.
intros.
generalize (list_split _ _ _ H0); intros.
inversion_clear H2 as [l1].
inversion_clear H3 as [l2].
subst l.
clear H0.
simpl in H1.
generalize (in_app_or _ _ _ H1); clear H1; intro X; inversion_clear X.
generalize (list_split _ _ _ H0); clear H0; intros.
inversion_clear H0 as [l1'].
inversion_clear H1 as [l2'].
subst l1.
simpl in H.
rewrite app_ass in H.
THeap_List_app_hyp H; clear H.
Decompose_sepcon H0 h1 h2.
generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H3); intros.
subst x.
assert (
   (((adr, size', status') :: l2') ++ (adr, size, status0) :: l2) = ((adr, size', status') :: (l2' ++ (adr, size, status0) :: l2))
).
intuition.
rewrite H2 in H3; clear H2.
assert (In (adr, size, status0) (l2' ++ (adr, size, status0) :: l2)).
intuition.
generalize (Heap_List_suiv_ge _ adr size status0 _ _ _ _ _ _ _  H3 H2); intro X.
assert (~(adr>adr)).
intros.
omega.
intuition.
simpl in H0.
inversion_clear H0.
injection H1.
auto.
generalize (list_split _ _ _ H1); clear H1; intros.
inversion_clear H0 as [l1'].
inversion_clear H1 as [l2'].
subst l2.
simpl in H.
THeap_List_app_hyp H; clear H.
Decompose_sepcon H0 h1 h2.
generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H3); intros.
subst x.
assert (In (adr, size', status') (l1' ++ (adr, size', status') :: l2')).
intuition.
generalize (Heap_List_suiv_ge _ adr size' status' _ _ _ _ _ _ _  H3 H2); intro X.
assert (~(adr>adr)).
intros.
omega.
intuition.
Qed.

Lemma Heap_List_list_split_cont: forall l adr size stat size' stat' startl s h,
    Heap_List l startl 0 s h ->
    In (adr, size, stat) l ->
    In (adr + 2 + size, size', stat') l ->
    (exists l1, exists l2, l = l1 ++ (adr, size, stat)::(adr + 2 + size, size', stat')::l2 ).
induction l.
simpl; contradiction.
induction a; induction a.
intros.
simpl in H0.
simpl in H1.
inversion_clear H0.
inversion_clear H1.
injection H2.
injection H0.
intros.
subst a.
assert (adr + 2 + size <> adr).
omega.
contradiction.
injection H2.
intros; subst a b0 b; clear H2.
inversion_clear H.

subst stat startl next0.
exists hl_nil.
simpl.
clear H7.
induction l.
simpl in H0; contradiction.
clear IHl0.
induction a; induction a.
simpl in H0.
inversion_clear H0.
injection H.
intros; subst a b0 b; clear H.
exists l.
auto.
generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H8); intros.
generalize (Heap_List_suiv_ge _ _ _ _ _ _ _ _ _ _ _ H8 H); intros.
subst a.
assert (~ (adr + 2 + size > adr + 2 + size)).
omega.
contradiction.

subst stat startl next0.
exists hl_nil.
simpl.
clear H7.
induction l.
simpl in H0; contradiction.
clear IHl0.
induction a; induction a.
simpl in H0.
inversion_clear H0.
injection H.
intros; subst a b0 b; clear H.
exists l.
auto.
generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H8); intros.
generalize (Heap_List_suiv_ge _ _ _ _ _ _ _ _ _ _ _ H8 H); intros.
subst a.
assert (~ (adr + 2 + size > adr + 2 + size)).
omega.
contradiction.

inversion_clear H1.
injection H0.
intros; subst a b0 b; clear H0.
generalize (Heap_List_suiv_ge _ _ _ _ _ _ _ _ _ _ _ H H2); intros.
assert (~ (adr > adr + 2 + size)).
omega.
contradiction.
inversion_clear H.

subst b startl next0.
generalize (IHl _ _ _ _ _ _ _ _ H9 H2 H0); intro.
inversion_clear H.
inversion_clear H4.
exists ((a,b0,Free)::x); exists x0.
rewrite H.
trivial.

subst b startl next0.
generalize (IHl _ _ _ _ _ _ _ _ H9 H2 H0); intro.
inversion_clear H.
inversion_clear H4.
exists ((a,b0,Allocated)::x); exists x0.
rewrite H.
trivial.
Qed.


Ltac Resolve_topsy:=
      (simpl; red; intuition; repeat (Store_update || Heap_List_equiv)).



Ltac Step  R :=
         match goal with
          | id: {{?P'}} ?c {{?Q'}} |- {{?P}} ?c {{?Q}} => eapply apply_triple; [apply id | idtac | idtac]
          | id: {{?P'}} ?c {{?Q'}} |- {{?P}} ?c; ?c' {{?Q}} => eapply apply_triple'; [apply id | idtac | idtac]
          | |- {{?P}} ?x <- ?e {{?Q}} => eapply semax_assign'
          | |- {{?P}} ?x <- ?e ; ?c {{?Q}} => eapply semax_assign'' with R; [red; intros | idtac]
          | |- {{?P}} ?x <-* ?e {{?Q}} => eapply semax_lookup_backwards'
          | |- {{?P}} ?x <-* ?e ; ?c {{?Q}} =>  eapply semax_lookup_backwards'' with R; [red; intros | idtac]
          | |- {{?P}} ?e1 *<- ?e2 {{?Q}} => eapply semax_mutation_backwards'
          | |- {{?P}} ?e1 *<- ?e2 ; ?c {{?Q}} => eapply semax_mutation_backwards'' with R; [red; intros | idtac]
          | |- {{?P}} while ?b ?c1 {{?Q}} => eapply semax_while' with R
          | |- {{?P}} while ?b ?c1 ; ?c2 {{?Q}} => eapply semax_while'' with R; [red; intros | idtac | idtac]
          | |- {{?P}} skip {{?Q}} =>  eapply semax_skip'
          | |- {{?P}} ifte ?b thendo ?c1 elsedo ?c2 {{?Q}} =>  eapply semax_ifte
          | |- {{?P}} (ifte ?b thendo ?c1 elsedo ?c2); ?c' {{?Q}} => apply semax_seq with R; [eapply semax_ifte; [idtac| idtac] | idtac]
          | |- {{?P}} ?c1; ?c2 {{?Q}} => apply semax_seq with R; [idtac| idtac]
         end.
