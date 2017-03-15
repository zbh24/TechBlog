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
Require Import topsy_hm_old.
Require Import topsy_hmAlloc_old.

Definition hmAlloc_example (result entry cptr fnd stts nptr sz:var.v) (v: Z):=

	(hmAlloc result 1 entry cptr fnd stts nptr sz);
	(ifte ((var_e result) =/= (nat_e 0)) thendo (

		((var_e result) *<- (int_e v))

	) elsedo (
		
		skip

	)).

Definition hmAlloc_example_specif :=
    forall (result entry cptr fnd stts nptr sz:var.v) (v: Z) x e startl,
    startl > 0 ->
    var.set (hmStart::result::entry::cptr::fnd::stts::nptr::sz::nil) ->
    {{ ((nat_e x) |-> (int_e e)) ** 
         (fun s => fun h => exists l,
             eval (var_e hmStart) s = eval (nat_e startl) s /\
             Heap_List l startl 0 s h /\ (In (x,1,Allocated) l)) }}
             
             hmAlloc_example result entry cptr fnd stts nptr sz v

    {{ fun s => fun h =>
         eval (var_e result) s <> eval (nat_e 0) s ->
         (((nat_e x) |-> (int_e e)) ** 
         (fun s => fun h => exists l,
             Heap_List l startl 0 s h /\ (In (x,1,Allocated) l)) ** (((var_e result) |-> (int_e v))) ** TT) s h}}.


Lemma hmAlloc_example_verif : hmAlloc_example_specif.
unfold hmAlloc_example_specif.
intros.
unfold hmAlloc_example.

Step (

(fun s => fun h => 
    (exists l, exists y, y > 0 /\ eval (var_e result) s = Z_of_nat (y+2) /\
      (exists size'', size'' >= 1 /\
      (Heap_List l startl 0 ** Array (y + 2) size'') s h /\ 
      In (x,1,Allocated) l /\ 
      In (y,size'',Allocated) l /\ 
      x <> y))

    \/

    (exists l, eval (var_e result) s = 0%Z /\ Heap_List l startl 0 s h /\ In (x,1,Allocated) l))

**

((nat_e x) |-> (int_e e))

).

Frame_rule ((nat_e x) |-> (int_e e)).

assert (1>0).
omega.
generalize (hmAlloc_verif1 result startl 1 x 1 entry cptr fnd stts nptr sz H0 H H1 H1); intros.
clear H1.
Step TT.
clear H2.
red; intros.
inversion_clear H1.
exists x0; tauto.
clear H2.
red; intros.
trivial.

red.
intros.
split; [intros; Mapsto | intros; Mapsto].

Step TT.
Step TT.
red; intros.
inversion_clear H1.
Decompose_sepcon H2 h1 h2.
inversion_clear H2.
inversion_clear H5 as [l].
inversion_clear H2 as [y].
decompose [and] H5; clear H5.
inversion_clear H9 as [size''].
decompose [and] H5; clear H5.
Decompose_sepcon H10 h11 h12.
assert (exists size, 1 + size = size'').
induction size''.
inversion H7.
exists size''; omega.
inversion_clear H14.
rewrite <- H16 in H15.
simpl in H15.
Decompose_sepcon H15 h121 h122.
inversion_clear H15.
exists (int_e x1).
Compose_sepcon h121 (h122 +++ h11 +++ h2).
Mapsto.
Intro_sepimp h'121 h'.
intros.
Compose_sepcon (h11 +++ h2 +++ h'121) h122.
Compose_sepcon (h11 +++ h2) h'121.
Compose_sepcon h2 h11.
Mapsto.
exists l.
auto.
Mapsto.
red; auto.
inversion_clear H5 as [l].
decompose [and] H2; clear H2.
assert (eval (var_e result) s <> 0)%Z.
Omega_exprb.
contradiction.

Step TT.

red; intros.
inversion_clear H1.
Decompose_sepcon H3 h1 h2.
assert (eval (var_e result) s = eval (nat_e 0) s).
Omega_exprb.
contradiction.
Qed.




