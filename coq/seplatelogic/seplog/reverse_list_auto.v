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

Load seplog_header.

Require Import Omega.
Require Import frag_list_entail.
Require Import frag_list_triple.
Require Import frag_list_vcg.

Require Import expr_b_dp.

Open Local Scope frag2_scope.

Coercion var_e : var.v >-> expr.
Coercion int_e : val >-> expr.
Coercion nat_e : nat >-> expr.

Definition next := 0%Z.
Definition data := 1%Z.
Definition i : var.v := 2.
Definition j : var.v := 3.
Definition k : var.v := 4.

Definition reverse_list_precond :=
  (true_b, lst i 0)::nil.

Definition reverse_list_postcond :=
  (true_b, lst j 0)::nil.

Definition invariant :=
  (
    (i == 0 , lst j 0)::
    (i =/= 0, star (lst i 0) (lst j 0))
    ::
    nil
  ).


Definition invariant_auto :=
  (
    ((i =/= 0) &&& (j == 0), (lst i 0))::
    ((j =/= 0) &&& (i == k), star (lst k 0) (lst j 0))
    ::
    nil
  ).


Definition invariant2 :=
  (
    (true_b, star (lst i 0) (lst j 0))
    ::
    nil
  ).


Definition reverse_list : cmd' :=
  (j <- 0);
  while' (i =/= 0) invariant2
    
  (

      (k <-* (i -.> next));
      ((i -.> next) *<- j);
      (j <- i);
      (i <- k)

  ).

Goal
  {{Assrt_interp reverse_list_precond}} (proj_cmd reverse_list) {{Assrt_interp reverse_list_postcond}}.
  eapply frag2_hoare_correct.

  compute.
  auto.
  Show Proof.
Qed.