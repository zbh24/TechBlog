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

Open Local Scope sep_scope.
Open Local Scope Z_scope.

Require Import topsy_hm_old.


Definition hmInit (adr: loc) (size:nat) :=
  hmStart <- (nat_e adr);
  hmStart -.> next *<- (nat_e adr) +e (nat_e size) -e (int_e 2);
  hmStart -.> status *<- Free;
  hmEnd <-* (hmStart -.> next);
  hmEnd -.> next *<- (int_e 0);
  hmEnd -.> status *<- Allocated.

Close Local Scope Z_scope.

Open Local Scope heap_scope.

(* hmInit Specification *)

Definition hmInit_specif := forall startp sizep,
   startp > 0 ->
   sizep > 4 ->
   {{ Array startp sizep}}
   
   hmInit startp sizep
   
   {{Heap_List ((startp, sizep - 4, Free)::nil) startp 0}}.

Lemma hmInit_verif : hmInit_specif.
unfold hmInit_specif.
unfold hmInit.
intros.
simpl.

eapply semax_assign'' with (fun s => fun h => Array startp sizep s h /\ eval (var_e hmStart) s = eval (nat_e startp) s).
red.
Resolve_topsy.
Array_equiv.


eapply semax_mutation_backwards'' with (fun s => fun h => 
(Array (startp) 1 ** ((nat_e (startp +1))|->(nat_e startp +e nat_e sizep -e int_e 2%Z)) ** Array (startp + 2) (sizep - 2) ) s h /\ 
eval (var_e hmStart) s = eval (nat_e startp) s).
red.
intros.
inversion_clear H1.
generalize (Array_concat_split  2 (sizep - 2) startp s h); intro X; inversion_clear X.
assert (2 + (sizep - 2) = sizep).
omega.
rewrite H5 in H1.
generalize (H1 H2); clear H1 H4 H5.
intros.
Decompose_sepcon H1 h1 h2.
Decompose_sepcon H4 h11 h12.
inversion_clear H6.
Decompose_sepcon H10 h121 h122.
red in H13; inversion_clear H10.
exists (int_e x0).
Compose_sepcon h121 (heap.union h11 h2).
unfold next.
Mapsto.
Intro_sepimp h121' h'.
split.
Compose_sepcon (heap.union h11 h121') h2.
Compose_sepcon h11 h121'.
simpl.
Compose_sepcon h11 heap.emp.
exists x.
intuition.
red; auto.
Mapsto.
simpl.
unfold next.
simpl in H3; rewrite H3.
Omega_exprb.
intuition.
intuition.
intuition.

eapply semax_mutation_backwards'' with (fun s => fun h => 
(((nat_e startp) |-> (Free)) ** ((nat_e (startp +1))|->(nat_e startp +e nat_e sizep -e int_e 2%Z)) ** Array (startp + 2) (sizep - 2) ) s h /\ 
eval (var_e hmStart) s = eval (nat_e startp) s).
red.
intros.
inversion_clear H1.
Decompose_sepcon H2 h1 h2.
Decompose_sepcon H2 h11 h12.
simpl in H5.
Decompose_sepcon H5 h111 h112.
red in H12.
inversion_clear H8.
exists (int_e x).
Compose_sepcon h111 (heap.union h12 h2).
Mapsto.
simpl in H3; rewrite H3; unfold status.
Omega_exprb.
Intro_sepimp h111' h'.
split.
Compose_sepcon (heap.union h111' h12) h2.
Compose_sepcon h111' h12.
Mapsto.
simpl.
simpl in H3; rewrite H3; unfold status.
Omega_exprb.
intuition.
intuition.
intuition.
intuition.

eapply semax_lookup_backwards'' with (fun s => fun h => 
(((nat_e startp) |-> (Free)) ** ((nat_e (startp +1))|->(nat_e startp +e nat_e sizep -e int_e 2%Z)) ** Array (startp + 2) (sizep - 2) ) s h /\ 
eval (var_e hmStart) s = eval (nat_e startp) s /\
eval (var_e hmEnd) s = eval (nat_e startp +e nat_e sizep -e int_e 2%Z) s).
red.
intros.
inversion_clear H1.
Decompose_sepcon H2 h1 h2.
simpl in H3.
Decompose_sepcon H2 h11 h12.
exists (nat_e startp +e nat_e sizep -e int_e 2%Z).
Compose_sepcon h12 (heap.union h11 h2).
Mapsto.
unfold next; rewrite H3.
Omega_exprb.
intuition.
Intro_sepimp h12' h'.
red.
split.
Compose_sepcon (heap.union h11 h12') h2.
Compose_sepcon h11 h12'.
intuition.
assert (h12 = h12').
eapply singleton_equal.
apply H9.
apply H10.
simpl.
unfold next; rewrite H3.
Omega_exprb.
intuition.
Mapsto.
simpl.
rewrite H3.
unfold next.
Omega_exprb.
simpl.
Array_equiv.
Store_update.
split.
simpl.
Store_update.
auto.


eapply semax_mutation_backwards'' with (fun s => fun h => 
(((nat_e startp) |-> (Free)) ** ((nat_e (startp +1))|->(nat_e startp +e nat_e sizep -e int_e 2%Z)) ** Array (startp + 2) (sizep - 4) ** Array (startp + sizep - 2) 1 ** ((nat_e startp +e nat_e sizep -e int_e 1%Z)|->(int_e 0%Z)) ) s h /\ 
eval (var_e hmStart) s = eval (nat_e startp) s /\
eval (var_e hmEnd) s = eval (nat_e startp +e nat_e sizep -e int_e 2%Z) s).
red.
intros.
decompose [and] H1; clear H1.
Decompose_sepcon H2 h1 h2.
Decompose_sepcon H2 h11 h12.
generalize (Array_concat_split  (sizep - 4) 2 (startp + 2) s h2); intro X; inversion_clear X.
assert ((sizep - 4 + 2) = sizep - 2).
omega.
rewrite H12 in H9.
generalize (H9 H7); clear H9 H11 H12; intros.
Decompose_sepcon H9 h21 h22.
Decompose_sepcon H14 h221 h222.
inversion_clear H14.
Decompose_sepcon H17 h2221 h2222.
red in H20.
inversion_clear H17.
assert (startp + 2 + (sizep - 4) +1 = startp + sizep - 1).
intuition.
rewrite H17 in H19.
exists (int_e x0).
clear H17.
clear H7.
Compose_sepcon h2221 (heap.union h221 (heap.union h21 (heap.union h12 h11))).
Mapsto.
simpl.
simpl in H5; rewrite H5.
unfold next.
Omega_exprb.
intuition.
Intro_sepimp h2221' h'.
split.
Compose_sepcon (heap.union h11 (heap.union h12 (heap.union h21 h221))) h2221'.
Compose_sepcon (heap.union h11 (heap.union h12 h21)) h221.
Compose_sepcon (heap.union h11 h12) h21. 
Compose_sepcon h11 h12.
intuition.
intuition.
intuition.
simpl.
Compose_sepcon h221 heap.emp.
exists x.
Mapsto.
simpl.
intuition.
intuition.
red; auto.
Mapsto.
simpl.
simpl in H5; rewrite H5.
unfold next.
Omega_exprb.
intuition.
intuition.

eapply semax_mutation_backwards'.
red.
intros.
decompose [and] H1; clear H1.
Decompose_sepcon H2 h1 h2.
Decompose_sepcon H2 h11 h12.
Decompose_sepcon H6 h111 h112.
Decompose_sepcon H9 h1111 h1112.
simpl in H10.
Decompose_sepcon H10 h121 h122.
red in H19.
inversion_clear H15.
exists (int_e x).
Compose_sepcon h121 (heap.union h2 (heap.union h112 (heap.union h1111 h1112))).
Mapsto.
simpl.
unfold status; simpl in H5; rewrite H5.
Omega_exprb.
intuition.
Intro_sepimp h121' h'.
eapply Heap_List_suiv_Free with (h1 := (heap.union h1111 (heap.union h1112 h112))) (h2 := heap.union h2 h121').
Disjoint_heap.
Equal_heap.
auto.
intuition.
auto.
auto.
Compose_sepcon (heap.union h1111 h1112) h112.
simpl.
Compose_sepcon h1111 h1112.
intuition.
Compose_sepcon h1112 heap.emp.
Mapsto.
red; auto.
intuition.
eapply Heap_List_last.
auto.
intuition.
intuition.
simpl.
Compose_sepcon h121' h2.
unfold status in H20.
Mapsto.
Compose_sepcon h2 heap.emp.
Mapsto.
simpl.
red; auto.
Qed.


