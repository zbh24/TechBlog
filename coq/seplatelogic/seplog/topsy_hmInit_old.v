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
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *)

Load seplog_header.

Open Local Scope sep_scope.
Open Local Scope Z_scope.

Require Import topsy_hm_old.
Require Import frag.


Definition hmInit (adr: loc) (size:nat) :=
  hmStart <- nat_e adr;
  hmStart -.> next *<- nat_e adr +e nat_e size -e int_e 2;
  hmStart -.> status *<- Free;
  hmEnd <-* hmStart -.> next;
  hmEnd -.> next *<- int_e 0;
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


Definition hmInit_precond (adr: loc) (size:nat):=
  (true_b,
      star
      (star (cell (nat_e adr)) (cell (nat_e adr +e int_e 1%Z)))
      (star (cell (nat_e adr +e nat_e size -e int_e 2%Z)) (cell (nat_e adr +e nat_e size -e int_e 1%Z)))
  ).

Definition hmInit_postcond (adr: loc) (size:nat):=
  (true_b,
      star
      (star (singl (nat_e adr) Free) (singl (nat_e adr +e int_e 1%Z) (nat_e adr +e nat_e size -e int_e 2%Z)))
      (star (singl (nat_e adr +e nat_e size -e int_e 2%Z) Allocated) (singl (nat_e adr +e nat_e size -e int_e 1%Z) (nat_e 0)))
  ).

(* hmInit Verification *)

Lemma hmInit_verif : hmInit_specif.
unfold hmInit_specif.
intros.
apply semax_strengthen_pre with (
   (assrt_interp (hmInit_precond startp sizep)) ** Array (startp + 2) (sizep - 4)
).

simpl; red; intros.
generalize (Array_concat_split (sizep - 2) 2 startp s h); intro A1; inversion_clear A1 as [A2 A3]; clear A3.
assert (A4:sizep - 2 + 2 = sizep); 
[OmegaZ | 
rewrite <- A4 in H1; clear A4; generalize (A2 H1); clear A2; intro A1].
Decompose_sepcon A1 h1 h2.
generalize (Array_concat_split 2 (sizep - 4) startp s h1); intro A1; inversion_clear A1 as [A2 A3]; clear A3.
assert (A4: 2 + (sizep - 4) = sizep - 2); 
[OmegaZ | 
rewrite <- A4 in H3; clear A4; generalize (A2 H3); clear A2; intro A1].
Decompose_sepcon A1 h11 h12.
Compose_sepcon (h11 +++ h2) h12; [idtac | auto].
split; auto.
Compose_sepcon h11 h2.
simpl in H7.
Decompose_sepcon H7 h111 h112.
Compose_sepcon h111 h112.
auto.
Decompose_sepcon H13 h1121 h1122.
inversion_clear H13.
exists x.
assert (A1:h1121 = h112); [Heap_emp_clean; Equal_heap | rewrite <- A1; Mapsto].
simpl in H6.
Decompose_sepcon H6 h21 h22.
Compose_sepcon h21 h22.
inversion_clear H9.
exists x.
Mapsto.
Decompose_sepcon H13 h221 h222.
inversion_clear H13.
exists x.
assert (A1:h221 = h22); [Heap_emp_clean; Equal_heap | rewrite <- A1; Mapsto].

apply semax_weaken_post with (
   (assrt_interp (hmInit_postcond startp sizep)) ** Array (startp + 2) (sizep - 4)
).
red; intros.
Decompose_sepcon H1 h1 h2.
simpl in H2.
inversion_clear H2.
Decompose_sepcon H6 h11 h12.

eapply Heap_List_suiv_Free with (h1 := (h11 +++ h2)) (h2 := h12); [Heap_emp_clean; Disjoint_heap | Heap_emp_clean; Equal_heap | auto | intuition | auto | auto | idtac | idtac].
simpl.
Compose_sepcon h11 h2; [idtac | auto].
Decompose_sepcon H6 h111 h112.
Compose_sepcon h111 h112; [Mapsto | idtac].
Compose_sepcon h112 heap.emp; [Mapsto | red; auto].

eapply Heap_List_last; [auto | intuition | omega | idtac].
simpl.
Decompose_sepcon H9 h121 h122.
Compose_sepcon h121 h122; [Mapsto | auto].
Compose_sepcon h122 heap.emp; [Mapsto | red; auto].

Frame_rule (Array (startp + 2) (sizep - 4)).

unfold hmInit_precond.
unfold hmInit_postcond.
eapply LWP_use.
simpl; intuition.
unfold hmStart; unfold hmEnd; unfold next; unfold status; unfold Allocated; unfold Free.
LWP_Resolve.

simpl.
eapply Array_inde_list.
Qed.

