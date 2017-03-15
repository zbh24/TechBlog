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

Require Import List.
Require Import ZArith.
Require Import List.
Require Import EqNat.
Require Import Classical.

Require Import util.
Require Import heap.
Require Import bipl.
Require Import axiomatic.
Require Import contrib.

Open Local Scope heap_scope.
Open Local Scope sep_scope.

(** weakest precondition generator *)

Inductive cmd' : Type :=
 skip': cmd'
| assign_var_e' : var.v -> expr -> cmd'
| assign_var_deref' : var.v -> expr -> cmd'
| assign_deref_expr' : expr -> expr -> cmd'
| malloc' : var.v -> expr -> cmd'
| free' : expr -> cmd'
| while' : expr_b -> assert -> cmd' -> cmd'
| seq' : cmd' -> cmd' -> cmd'
| ifte' : expr_b -> cmd' -> cmd' -> cmd'.

Fixpoint proj_cmd (c':cmd') : cmd :=
  match c' with
    skip' => skip
    |  assign_var_e' x e => x <- e
    | assign_var_deref' x e => x <-* e
    | assign_deref_expr' e f => e *<- f
    | malloc' x e => x <-malloc e
    | free' e => free e
    | while' b Q c''  => while b (proj_cmd c'')
    | seq' c1 c2 => (seq (proj_cmd c1) (proj_cmd c2))
    | ifte' b c1 c2 => (ifte b thendo (proj_cmd c1) elsedo (proj_cmd c2))
  end.

Notation "x <- e" := (assign_var_e' x e) (at level 80) : vc_scope.
Notation "x '<-*' e" := (assign_var_deref' x e) (at level 80) : vc_scope.
Notation "e '*<-' f" := (assign_deref_expr' e f) (at level 80) : vc_scope.
Notation "x '<-malloc' e" := (malloc' x e) (at level 80) : vc_scope.
Notation "c ; d" := (seq' c d) (at level 81, right associativity) : vc_scope.
Notation "'ifte' a 'thendo' x 'elsedo' y" := (ifte' a x y)(at level 80) : vc_scope.

Open Local Scope vc_scope.

(* compute the weakest precondition under the assumption that 
while loops are annotated with invariants *)
Fixpoint wp (c:cmd') (P:assert) {struct c} : assert :=
  match c with
    skip' => P
    | assign_var_e' x e => update_store2 x e P
    | assign_var_deref' x e => 
      fun s h => exists e0, ((e |-> e0) ** ((e |-> e0) -* (update_store2 x e0 P))) s h
    | assign_deref_expr' e f =>  
      fun s h => exists x, (((e |-> x) ** ((e |-> f) -* P)) s h)
    | (malloc' x e) => 
      fun s h => forall n, (((nat_e n) |-> e) -* (update_store2 x (nat_e n) P)) s h
    | free' e => fun s h => 
      exists l, val2loc (eval e s) = l /\
	exists v, heap.lookup l h = Some v /\
	  P s (h --- l)
    | while' b Q c' => Q
    | seq' c1 c2 => wp c1 (wp c2 P)
    | ifte' b c1 c2 => (fun s h =>
      ( eval_b b s = true -> (wp c1 P) s h) /\ 
      ( eval_b b s = false -> (wp c2 P) s h))
  end.

(* condition on the goal *)
Fixpoint vc (c:cmd') (P:assert) {struct c} : assert :=
  match c with
    skip' => TT
    | assign_var_e' x e => TT
    | assign_var_deref' x e => TT
    | assign_deref_expr' e f => TT
    | malloc' x e => TT
    | free' e => TT
    | while' b Q c' => fun s h =>
      (Q s h /\ eval_b b s = false -> P s h) /\
      (Q s h /\ eval_b b s = true -> (wp c' Q) s h) /\
      ((vc c' Q) s h)
    | seq' c1 c2 => fun s h =>
      vc c1 (wp c2 P) s h /\ (vc c2 P) s h
    | ifte' b c1 c2 => fun s h =>
      (vc c1 P) s h /\ (vc c2 P) s h
  end.

Lemma vc_soundness : forall c' P,
    (forall s h, vc c' P s h) -> {{wp c' P}} (proj_cmd c') {{ P }}.
induction c'.
intros.
simpl.
apply semax_skip.
intros.
simpl.
apply semax_assign.
intros.
simpl.
apply  semax_lookup_backwards.
intros.
simpl.
apply semax_mutation_backwards.
intros.
simpl.
apply semax_malloc.
intros.
simpl.
apply semax_free.
intros.
simpl.
apply semax_weaken_post with (fun s => fun h =>
(a s h) /\ (eval_b e s)=false).
unfold sep.entails; intros.
generalize (H s h); simpl; intro.
intuition.
apply semax_while.
apply semax_strengthen_pre with (wp c' a).
unfold sep.entails ; intros.
generalize (H s h); simpl; intro.
intuition.
apply IHc'.
generalize (IHc' a); intro.
intros.
generalize (H s h); simpl; intro.
intuition.
intros.
simpl.
apply semax_seq with (wp c'2 P).
apply IHc'1.
intros.
generalize (H s h); intro.
simpl in H0.
intuition.
apply IHc'2.
intros.
generalize (H s h); intro.
simpl in H0.
intuition.
intros.
simpl.
apply semax_ifte.
apply semax_strengthen_pre with (wp c'1 P).
unfold sep.entails ; intros.
intuition.
apply IHc'1.
intros.
generalize (H s h); simpl; intro.
intuition.
apply semax_strengthen_pre with (wp c'2 P).
unfold sep.entails ; intros.
intuition.
apply IHc'2.
intros.
generalize (H s h); simpl; intros.
intuition.
Qed.

Lemma wp_vc_util: forall c Q P , 
   (forall s h, vc c Q s h) -> (P ==> wp c Q) -> {{P}} proj_cmd c {{Q}}.
intros.
apply (semax_strengthen_pre P (wp c Q) Q (proj_cmd c) H0 (vc_soundness c Q H)).
Qed.

Close Local Scope vc_scope.
