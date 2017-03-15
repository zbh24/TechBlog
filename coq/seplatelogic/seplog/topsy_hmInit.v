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

Require Import topsy_hm.
Require Import frag.

(****************************************************************************)

(* this file contains the verification of hmInit in two flavors:
  1. semi-automatic using the "frag" tactic
  2. manual
    *)

(****************************************************************************)

(*
 65 Error hmInit(Address addr)
 66 {
 67     start = (HmEntry)addr;
 68     start->next = (HmEntry)((unsigned long)addr + KERNELHEAPSIZE + 
 69                                                             sizeof(HmEntryDesc));
 70     start->status = HM_FREED;
 71     
 72     end = start->next;
 73     end->next = NULL;
 74     end->status = HM_ALLOCATED;
 75     
 76     hmLock = &hmLockDesc;
 77     lockInit( hmLock);
 78     
 79     return HM_INITOK;
 80 }
*)
Definition hmInit (adr:loc) (size:nat) :=
  hmStart <- (nat_e adr);
  hmStart -.> next *<- (nat_e adr) +e (nat_e size) -e (int_e 2%Z);
  hmStart -.> status *<- Free;
  hmEnd <-* (hmStart -.> next);
  hmEnd -.> next *<- (int_e 0%Z);
  hmEnd -.> status *<- Allocated.

Definition hmInit_specif := forall p size, size >= 4 ->
   {{ Array p size }}
   hmInit p size
   {{ Heap_List ((size - 4, free)::nil) p }}.

Definition hmInit_precond (adr:loc) (size:nat):=
  (true_b,
      star
      (star (cell (nat_e adr)) (cell (nat_e adr +e int_e 1%Z)))
      (star (cell (nat_e adr +e nat_e size -e int_e 2%Z)) (cell (nat_e adr +e nat_e size -e int_e 1%Z)))
  ).

Definition hmInit_postcond (adr:loc) (size:nat):=
  (true_b,
      star
      (star (singl (nat_e adr) Free) (singl (nat_e adr +e int_e 1%Z) (nat_e adr +e nat_e size -e int_e 2%Z)))
      (star (singl (nat_e adr +e nat_e size -e int_e 2%Z) Allocated) (singl (nat_e adr +e nat_e size -e int_e 1%Z) (nat_e 0)))
  ).

Lemma frag_precond: forall startp sizep, sizep >= 4 ->
   Array startp sizep ==> (assrt_interp (hmInit_precond startp sizep)) ** Array (startp + 2) (sizep - 4).
red; intros.
TArray_concat_split_l_l 2 H; clear H0.
Decompose_sepcon H1 h1 h2.
TArray_concat_split_l_r 2 H4; clear H4.
Decompose_sepcon H3 h21 h22.
Compose_sepcon (h1 +++ h22) h21.
simpl.
split; auto.
Compose_sepcon h1 h22.
simpl in H1.
Decompose_sepcon H1 h11 h12.
Decompose_sepcon H10 h121 h122.
Compose_sepcon h11 h121; auto.
inversion_clear H10; exists x; Mapsto.
simpl in H7.
Decompose_sepcon H7 h221 h222.
Decompose_sepcon H10 h2221 h2222.
Compose_sepcon h221 h2221; auto.
inversion_clear H7 as [x]; exists x; Mapsto.
inversion_clear H10 as [x]; exists x; Mapsto.
Array_equiv.
Qed.

Lemma frag_postcond: forall startp sizep, sizep >= 4 ->
  (assrt_interp (hmInit_postcond startp sizep)) ** Array (startp + 2) (sizep - 4) ==> Heap_List ((sizep - 4, true)::nil) startp.
  red; intros.
  Decompose_sepcon H0 h1 h2.
  simpl in H1.
  inversion_clear H1.
  clear H3.
  Decompose_sepcon H5 h11 h12.
  Compose_sepcon (h11 +++ h2) h12.
  eapply hl_Free with (h1 := h11 +++ h2) (h2 := heap.emp); [Disjoint_heap | Equal_heap | auto | intuition | idtac | idtac].
  Decompose_sepcon H3 h111 h112.
  Compose_sepcon h11 h2; [idtac | Array_equiv].
  simpl; Compose_sepcon h111 h112; try Mapsto.
  Compose_sepcon h112 heap.emp; [Mapsto | red; auto].
  eapply hl_last; red; auto.
  Decompose_sepcon H7 h121 h122.
  simpl; Compose_sepcon h121 h122; try Mapsto.
  Compose_sepcon h122 heap.emp; [Mapsto | red; auto].
Qed.

Lemma hmInit_verif_auto : hmInit_specif.
  unfold hmInit_specif.
  unfold hmInit.
  intros.
  eapply semax_weaken_post.
  apply (frag_postcond p size H).
  eapply semax_strengthen_pre.
  apply (frag_precond p size H).
  Frame_rule (Array (p + 2) (size - 4)); [idtac | eapply Array_inde_list].
  unfold hmInit_precond; unfold hmInit_postcond; unfold hmStart; unfold hmEnd; unfold next; unfold status; unfold Allocated; unfold Free.
  eapply LWP_use.
  simpl; intuition.
  LWP_Resolve.
Qed.

Lemma hmInit_verif_manual : hmInit_specif.
  unfold hmInit_specif.
  unfold hmInit.
  intros.
  
  Step (fun s h => Array p size s h /\ ( s |b= var_e hmStart == nat_e p)).
  red.
  split.
  eapply Array_inde_store.
  apply H0.
  rewrite <- expr_b_store_update_rewrite.
  Omega_exprb.
  
  Step ( fun s h =>
    (Array p 1 ** 
      ((var_e hmStart +e nat_e 1) |-> (nat_e p +e nat_e size -e int_e 2%Z)) ** Array (p + 2) (size - 2)) s h /\
    ( s |b= (var_e hmStart == nat_e p))
  ).
  inversion_clear H0.
  TArray_concat_split_l_l 2 H2.
  Decompose_sepcon H0 h1 h2.
  simpl in H3.
  Decompose_sepcon H3 h11 h12.
  Decompose_sepcon H9 h121 h122.
  inversion_clear H9.
  exists (int_e x).
  Compose_sepcon h121 (h2 +++ h11).
  unfold next.
  Mapsto.
  Intro_sepimp h121' h'.
  split.
  Compose_sepcon (h11 +++ h121') h2.
  Compose_sepcon h11 h121'.
  Compose_sepcon h11 heap.emp.
  auto.
  simpl; red; auto.
  unfold next in H13.
  Mapsto.
  auto.
  auto.
  
  Step ( fun s h =>
    (((var_e hmStart) |-> Free) ** 
      (var_e hmStart +e nat_e 1 |-> (nat_e p +e nat_e size -e int_e 2%Z)) ** Array (p + 2) (size - 2)) s h /\
    ( s |b= (var_e hmStart == nat_e p))
  ).
  inversion_clear H0.
  Decompose_sepcon H1 h1 h2.
  Decompose_sepcon H1 h11 h12.
  simpl in H4.
  Decompose_sepcon H4 h111 h112.
  inversion_clear H7.
  exists (int_e x).
  Compose_sepcon h111 (h12 +++ h2).
  unfold status; Mapsto.
  Intro_sepimp h111' h'.
  split.
  Compose_sepcon (h111' +++ h12) h2.
  Compose_sepcon h111' h12.
  unfold status in H12; Mapsto.
  auto.
  auto.
  auto.

  Step ( fun s h =>
    (((var_e hmStart) |-> Free) ** 
      ((var_e hmStart +e nat_e 1) |-> (nat_e p +e nat_e size -e int_e 2%Z)) ** Array (p + 2) (size - 2)) s h /\
    ( s |b= (var_e hmStart == nat_e p)) /\
    ( s |b= (var_e hmEnd == (nat_e p +e nat_e size -e int_e 2%Z)))
  ).
  inversion_clear H0.
  Decompose_sepcon H1 h1 h2.
  Decompose_sepcon H1 h11 h12.
  exists ((nat_e p +e nat_e size) -e int_e 2%Z).
  Compose_sepcon h12 (h11 +++ h2).
  unfold next; Mapsto.
  Intro_sepimp h12' h'.
  red.
  split.
  Compose_sepcon (h11 +++ h12') h2.
  Compose_sepcon h11 h12'.
  eapply mapsto_store_update_rewrite.
  simpl.
  Mapsto.
  eapply mapsto_store_update_rewrite.
  simpl.
  Mapsto.
  Array_equiv.
  split.
  rewrite <- expr_b_store_update_rewrite.
  Omega_exprb.
  rewrite <- expr_b_store_update_rewrite.
  Omega_exprb.

  Step ( fun s h =>
    (((var_e hmStart) |-> Free) ** 
      ((var_e hmStart +e nat_e 1) |-> (nat_e p +e nat_e size -e int_e 2%Z)) ** Array (p + 2) (size - 4) ** Array (p + size - 2) 1 ** ((var_e hmEnd +e nat_e 1)|->int_e 0%Z)) s h /\
    ( s |b= (var_e hmStart == nat_e p)) /\
    ( s |b= (var_e hmEnd == (nat_e p +e nat_e size -e int_e 2%Z)))
  ).
  decompose [and] H0; clear H0.
  Decompose_sepcon H1 h1 h2.
  Decompose_sepcon H1 h11 h12.
  TArray_concat_split_l_l (size - 4) H6.
  Decompose_sepcon H8 h21 h22.
  assert (size - 2 - (size - 4) = 2).
  omega.
  rewrite H12 in H13; clear H12.
  simpl in H13.
  Decompose_sepcon H13 h221 h222.
  Decompose_sepcon H16 h2221 h2222.
  inversion_clear H16.
  exists (int_e x).
  Compose_sepcon h2221 (h221 +++ h21 +++ h1).
  unfold next; Mapsto.
  Intro_sepimp h2221' h'.
  split.
  Compose_sepcon (h221 +++ h21 +++ h1) h2221'.
  Compose_sepcon (h21 +++ h1) h221.
  Compose_sepcon h1 h21.
  Compose_sepcon h11 h12.
  Mapsto.
  Mapsto.
  Array_equiv.
  simpl; auto.
  Compose_sepcon h221 heap.emp.
  inversion_clear H13.
  exists x0; Mapsto.
  red; auto.
  unfold next in h21; Mapsto.
  split; Omega_exprb.
  
  Step TT.
  red; intros.
  decompose [and] H0; clear H0.
  Decompose_sepcon H1 h1 h2.
  Decompose_sepcon H1 h11 h12.
  Decompose_sepcon H5 h111 h112.
  Decompose_sepcon H8 h1111 h1112.
  simpl in H9.
  Decompose_sepcon H9 h121 h122.
  inversion_clear H14.
  exists (int_e x).
  Compose_sepcon h121 (h122 +++ h11 +++ h2).
  unfold status; Mapsto.
  Intro_sepimp h121' h'.
  Compose_sepcon (h11 +++ h122) (h121' +++ h2).
  eapply hl_Free with (h1 := h11 +++ h122) (h2 := heap.emp).
  Disjoint_heap.
  Equal_heap.
  auto.
  intuition.
  Compose_sepcon (h1111 +++ h1112) h112.
  Compose_sepcon h1111 h1112.
  Mapsto.
  Compose_sepcon h1112 heap.emp.
  Mapsto.
  simpl; red; auto.
  auto.
  eapply hl_last.
  red; auto.
  simpl.
  Compose_sepcon h121' h2.
  unfold status in H19; Mapsto.
  Compose_sepcon h2 heap.emp.
  Mapsto.
  red; auto.
Qed.

