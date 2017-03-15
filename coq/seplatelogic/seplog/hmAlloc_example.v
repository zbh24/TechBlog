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
Require Import topsy_hmAlloc.
Require Import Bool.

Definition hmAlloc_example (result entry cptr fnd stts nptr sz:var.v) (v:val) :=
hmAlloc result 1 entry cptr fnd stts nptr sz;
ifte (var_e result =/= nat_e 0) thendo (
  (var_e result *<- int_e v)
) elsedo (
  skip
).

Definition hmAlloc_example_specif := forall v x e p, p > 0 ->
{{ (nat_e x |-> int_e e) ** (fun s h => exists l,
  (s |b= var_e hmStart == nat_e p) /\
  Heap_List l p s h /\ In_hl l (x,1,alloc) p) }}
hmAlloc_example result entry cptr fnd stts nptr sz v
{{ fun s h => s |b= var_e result =/= nat_e 0 ->
  ((nat_e x |-> int_e e) ** (fun s h => exists l,
  Heap_List l p s h /\ In_hl l (x,1,alloc) p) ** 
  (var_e result |-> int_e v) ** TT) s h}}.

Lemma hmAlloc_example_verif : hmAlloc_example_specif.
unfold hmAlloc_example_specif.
intros.
unfold hmAlloc_example.

Step ((fun s h => 
    (exists l, exists y, y > 0 /\ (s |b= (var_e result) == nat_e (y+2)) /\
      (exists size'', size'' >= 1 /\
      (Heap_List l p ** Array (y + 2) size'') s h /\ 
      In_hl l (x,1,alloc) p /\ 
      In_hl l (y,size'',alloc) p /\ 
      x <> y))
    \/
    (exists l, (s |b= (var_e result) == nat_e 0) /\ Heap_List l p s h /\ In_hl l (x,1,alloc) p))
**
(nat_e x |-> int_e e)
).

Frame_rule (nat_e x |-> int_e e).

assert (1>0).
omega.
generalize (hmAlloc_verif p x 1 1 H H0); intros.
clear H0.
Step TT.
red; intros.
Decompose_hyp.
exists x0.
Resolve_topsy.
clear H1.
red; intros.
inversion_clear H0.
left.
Decompose_hyp.
exists x0.
exists x1.
Resolve_topsy.
exists x2.
Resolve_topsy.
Compose_sepcon H1 H5; auto.
Decompose_hyp.
right.
exists x0.
Resolve_topsy.

red.
intros.
split; [intros; Mapsto | intros; Mapsto].

Step TT.
Step TT.

red; intros.
Decompose_hyp.
inversion_clear H4.
Decompose_hyp.
TArray_concat_split_l_l 1 H18.
Decompose_sepcon H17 h1 h2.
Decompose_sepcon H19 h11 h12.
inversion_clear H21.
exists (int_e x3).
Compose_sepcon h11 (h2 +++ H6 +++ H1).
Mapsto.
Intro_sepimp h11' h'.
intros.
Compose_sepcon (h11' +++ H6 +++ H1) h2.
Compose_sepcon (H6 +++ H1) h11'; try Mapsto.
Compose_sepcon H1 H6; try Mapsto.
exists x0.
auto.
red; auto.
Decompose_hyp.
Omega_exprb.

Step TT.
red; intros.
Decompose_hyp.
Omega_exprb.
Qed.




