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
Require Import frag_examples_old.

Definition hmInit (adr: loc) (size:nat) :=
  hmStart <- (nat_e adr);
  hmStart -.> next *<- (nat_e adr) +e (nat_e size) -e (int_e 2);
  hmStart -.> status *<- Free;
  hmEnd <-* (hmStart -.> next);
  hmEnd -.> next *<- (int_e 0);
  hmEnd -.> status *<- Allocated.

Close Local Scope Z_scope.

Open Local Scope heap_scope.


(* hmInit *)

(* hmInit Specification *)

Definition hmInit_specif := forall startp sizep,
   startp > 0 ->
   sizep > 4 ->
   {{ Array startp sizep}}
   
   hmInit startp sizep
   
   {{Heap_List ((startp, sizep - 4, Free)::nil) startp 0}}.

(* hmInit Verification *)


Lemma hmInit_verif : hmInit_specif.
unfold hmInit_specif.
intros.
generalize (hmInit_verif startp sizep); intros.
apply semax_strengthen_pre with (
Array startp 2 ** Array (startp + 2) (sizep - 4) ** Array (startp + sizep - 2) 2
).
red; intros.
generalize (Array_concat_split (sizep - 2) 2 startp s h); intro A1; inversion_clear A1 as [A2 A3]; clear A3.
assert (A4:sizep - 2 + 2 = sizep); 
[OmegaZ | 
rewrite <- A4 in H2; clear A4; generalize (A2 H2); clear A2; intro A1].
Decompose_sepcon A1 h1 h2.
Compose_sepcon h1 h2.
generalize (Array_concat_split 2 (sizep - 4) startp s h1); intro A1; inversion_clear A1 as [A2 A3]; clear A3.
assert (A4: 2 + (sizep - 4) = sizep - 2); 
[OmegaZ | 
rewrite <- A4 in H4; clear A4; generalize (A2 H4); clear A2; intro A1].
Decompose_sepcon A1 h11 h12.
Compose_sepcon h11 h12.
auto.
auto.
assert (A1: startp + sizep - 2 = startp + (sizep - 2)); [omega | rewrite A1; clear A1; auto].
apply semax_weaken_post with (
((nat_e startp) |-> Free) **
((nat_e (startp + 1)) |-> (nat_e (startp + sizep - 2))) **
(Array (startp + 2) (sizep - 4)) **
((nat_e (startp + sizep - 1)) |-> Allocated) ** 
((nat_e (startp + sizep - 2)) |-> (nat_e 0))
).
red; intros.
Decompose_sepcon H2 h1 h2.
Decompose_sepcon H3 h11 h12.
Decompose_sepcon H5 h111 h112.
Decompose_sepcon H8 h1111 h1112.
eapply Heap_List_suiv_Free with (h1 := h11) (h2 := h2 +++ h12); [Disjoint_heap | Equal_heap | intuition | intuition | auto | auto| idtac | idtac].
Compose_sepcon h111 h112. 
simpl.
Compose_sepcon h1111 h1112.
Mapsto.
Compose_sepcon h1112 heap.emp; [Mapsto | red; auto].
auto.
eapply Heap_List_last.
auto.
intuition.
omega.
Compose_sepcon h2 h12.
Mapsto.
simpl.
Compose_sepcon h12 heap.emp.
Mapsto.
red; auto.
Frame_rule (Array (startp + 2) (sizep - 4)).
Step TT.
simpl.
red; intros.
Decompose_sepcon H2 h1 h2.
Decompose_sepcon H3 h11 h12.
Decompose_sepcon H6 h21 h22.
Decompose_sepcon H9 h121 h122.
Decompose_sepcon H12 h221 h222.
split; auto.
Compose_sepcon (h21 +++ h221) (h11 +++ h121).
Compose_sepcon h21 h221.
auto.
inversion_clear H14.
exists x.
Mapsto.
Compose_sepcon h11 h121.
inversion_clear H5.
exists x.
Mapsto.
inversion_clear H11.
exists x.
Mapsto.
red; intros.
simpl in H2.
inversion_clear H2.
Decompose_sepcon H4 h1 h2.
Decompose_sepcon H4 h11 h12.
Decompose_sepcon H7 h21 h22.
Compose_sepcon h2 h1.
Compose_sepcon h22 h21.
Mapsto.
Mapsto.
Compose_sepcon h11 h12.
Mapsto.
Mapsto.
simpl.
eapply Array_inde_list.
Qed.

