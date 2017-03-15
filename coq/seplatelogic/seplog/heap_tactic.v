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

(* Tactic for decision on disjointness equality over heap *)

Open Local Scope heap_scope.

Lemma disjoint_up: forall x x1 x2 x3,
  x = x1 +++ x3 -> x1 # x3 -> x # x2 -> x1 # x2.
  intros.
  apply heap.equal_union_disjoint with x3.
  rewrite <-H.
  auto.
Qed.

Lemma disjoint_up': forall x x1 x2 x3,
  x = heap.union x1 x3 -> heap.disjoint x1 x3 -> heap.disjoint x x2 -> heap.disjoint x3 x2.
  intros.
  apply heap.equal_union_disjoint with x1.
  assert ((x1 +++ x3) = (x3 +++ x1)).
  apply heap.union_com.
  auto.
  rewrite <-H2.
  rewrite <-H.
  auto.
Qed.

Ltac Disjoint_heap :=
  match goal with
    | id: (?x1 +++ ?x2) # ?x |- _ => generalize (heap.disjoint_union' x1 x2 x (heap.disjoint_com (x1 +++ x2) x id)); intro Disjoint_heapA; inversion_clear Disjoint_heapA; clear id; Disjoint_heap
    | id: ?x # (?x1 +++ ?x2) |- _ => generalize (heap.disjoint_union' x1 x2 x id); intro Disjoint_heapA; inversion_clear Disjoint_heapA; clear id; Disjoint_heap
    |  |- (?x1 +++ ?x2) # ?x3 => eapply heap.disjoint_com; eapply heap.disjoint_union; split; [ (Disjoint_simpl || Disjoint_heap) | (Disjoint_simpl || Disjoint_heap)]
    |  |- ?x3 # (?x1 +++ ?x2) => eapply heap.disjoint_union; split; [ (Disjoint_simpl || Disjoint_heap) | (Disjoint_simpl || Disjoint_heap)]
    |  |- ?x1 # ?x2 => Disjoint_up
  end
with
  Disjoint_up :=
  (
    Disjoint_simpl ||  (Disjoint_up_left) || (Disjoint_up_right)
  )
with
  Disjoint_up_left :=
  match goal with
    | id1:  ?X1 = (?x1 +++ ?x1')  |- ?x1 # ?x2 => apply (disjoint_up X1 x1 x2 x1' id1); [(Disjoint_simpl || Disjoint_heap)|(Disjoint_simpl || Disjoint_heap)]
    | id1:  ?X1 = (?x1 +++ ?x1')  |- ?x1' # ?x2 => apply (disjoint_up' X1 x1 x2 x1' id1) ; [(Disjoint_simpl || Disjoint_heap)|(Disjoint_simpl || Disjoint_heap)]
    |  |- ?x1 # ?x2 => (Disjoint_simpl)
  end
with
  Disjoint_up_right :=
  match goal with
    | id1: ?X1 = (?x2 +++ ?x2')  |- ?x1 # ?x2 => apply heap.disjoint_com; apply (disjoint_up X1 x2 x1 x2' id1); [(Disjoint_simpl || Disjoint_heap)|(Disjoint_simpl || Disjoint_heap)]
    | id1: ?X1 = (?x2 +++ ?x2')  |- ?x1 # ?x2' => apply heap.disjoint_com; apply (disjoint_up' X1 x2 x1 x2' id1) ; [(Disjoint_simpl || Disjoint_heap)|(Disjoint_simpl || Disjoint_heap)]
    |  |- ?x1 # ?x2 => (Disjoint_simpl)
  end
with
  Disjoint_simpl :=
  match goal with
    | id : ?x1 # ?x2 |- ?x1 # ?x2 => auto
    | id : ?x2 # ?x1 |- ?x1 # ?x2 => apply heap.disjoint_com; auto
    | |- ?x1 # heap.emp => apply (heap.disjoint_emp x1)
    | |- heap.emp # ?x1 => apply heap.disjoint_com; apply (heap.disjoint_emp x1)
    | |- heap.singleton ?l1 ?v1 # heap.singleton ?l2 ?v2 => eapply heap.disjoint_singleton; omega
  end.

(* Test for the tatcic *)

Lemma tactic_test_disjoint: forall h h1 h2 h11 h12 h21 h22 h111 h112 h121 h122 h211 h212 h221 h222,
  h1 # h2 ->
  h11 # h12 ->
  h21 # h22 ->
  h111 # h112 ->
  h121 # h122 ->
  h211 # h212 ->
  h221 # h222 ->
  h = (heap.union h1 h2) ->
  h1 = (heap.union h11 h12) ->
  h2 = (heap.union h21 h22) ->
  h11 = (heap.union h111 h112) ->
  h12 = (heap.union h121 h122) ->
  h21 = (heap.union h211 h212) ->
  h22 = (heap.union h221 h222) ->
  (h112 +++ h221) # h222.
  intros.
  Disjoint_heap.
Qed.

Lemma tactic_test_disjoint2: forall h h1 h2,
  heap.disjoint h (heap.union h1 h2) ->
  heap.disjoint h h2 .
  intros.
  Disjoint_heap.
Qed.

(* Lemmas for the Equality tactic *)

Lemma equal_tactic_l1: forall h1 h2 h3 h4,
  heap.disjoint h1 h2 ->
  (heap.union h2 h1) = (heap.union h3 h4) ->
  (heap.union h1 h2) = (heap.union h3 h4).
  intros.
  apply trans_eq with (heap.union h2 h1).
  apply heap.union_com.
  auto.
  auto.
Qed.

Lemma equal_tactic_l1': forall h1 h2 h3 h4,
  heap.disjoint h3 h4 ->
  (heap.union h1 h2) = (heap.union h4 h3) ->
  (heap.union h1 h2) = (heap.union h3 h4).
  intros.
  apply trans_eq with (heap.union h4 h3).
  auto.
  apply heap.union_com.
  Disjoint_heap.
Qed.

Lemma equal_tactic_l2: forall h1 h2 h3 H,
  H = heap.union (heap.union h1 h2) h3 ->
  H = heap.union h1 (heap.union h2 h3).
  intros.
  rewrite H0.
  apply sym_eq.
  apply heap.union_assoc.
Qed.

Lemma equal_tactic_l2': forall h1 h2 h3,
  heap.union (heap.union h1 h2) h3 = heap.union h1 (heap.union h2 h3).
  intros.
  apply sym_eq.
  apply heap.union_assoc.
Qed.

Lemma equal_tactic_l3: forall h1 h2 h3 H,
        (heap.union (heap.union h1 h2) h3) = H  ->
              (heap.union h1 (heap.union h2 h3)) = H.
intros.
rewrite <- H0.
apply heap.union_assoc.
Qed.

Lemma equal_tactic_l4: forall x1 x2 h1 h2 H,
        H = (heap.union x1 x2) ->
              (heap.union x1 x2) = (heap.union h1 h2) ->
                  (heap.union h1 h2) = H.
intros.
rewrite H0.
rewrite H1.
auto.
Qed.

Lemma equal_tactic_l4': forall x1 h1 h2 H,
        H = x1 ->
              x1 = (heap.union h1 h2) ->
                  (heap.union h1 h2) = H.
intros.
rewrite H0.
rewrite H1.
auto.
Qed.

Lemma equal_tactic_l5: forall x1 x2 h1 h2 H,
        H = (heap.union x1 x2) ->
              (heap.union x1 x2) = (heap.union h1 h2) ->
                  H = (heap.union h1 h2).
intros.
rewrite H0.
rewrite H1.
auto.
Qed.

Lemma equal_tactic_l5': forall x1 h1 h2 H,
        H = x1 ->
              x1 = (heap.union h1 h2) ->
                  H = (heap.union h1 h2).
intros.
rewrite H0.
rewrite H1.
auto.
Qed.

Lemma equal_tactic_l6: forall X Y,
     X = Y ->
         (heap.union X heap.emp) = Y.
intros.
rewrite H.
apply heap.equal_union_emp.
Qed.

Lemma equal_tactic_l7: forall X Y,
      Y = X ->
         (heap.union heap.emp X ) = Y.
intros.
subst X.
apply trans_eq with (heap.union Y heap.emp).
apply heap.union_com.
apply heap.disjoint_com.
apply heap.disjoint_emp.
apply heap.equal_union_emp.
Qed.

Lemma equal_tactic_l8: forall x1 x2 h1 X Y,
  X = x1 +++ x2 ->
  h1 # X ->
  x1 # x2 ->
  h1 +++ (x1 +++ x2) =  Y ->
  h1 +++ X = Y.
  intros.
  subst X Y.
  auto.
Qed.

Lemma equal_tactic_l8': forall x1 h1 X Y,
  X = x1 ->
  heap.disjoint h1 X ->
  (heap.union h1 x1) = Y ->
  (heap.union h1 X) = Y.
  intros.
  subst X Y.
  auto.
Qed.

Lemma equal_tactic_l9: forall X Y h1,
            h1 = X ->
               X = Y ->
                  (heap.union X h1) = (heap.union Y h1).
intros.
subst X Y.
auto.
Qed.

Lemma equal_tactic_l9': forall X Y x1 x2,
      x1 = x2 ->
            heap.disjoint x1 X ->
            heap.disjoint x2 X ->
               X = Y ->
                  (heap.union X x1) = (heap.union Y x2).
intros.
subst Y x1.
auto.
Qed.

Lemma equal_tactic_l10: forall X h1 h2,
            h1 = h2 ->
                  (heap.union X h1) = (heap.union X h2).
intros.
subst h1.
auto.
Qed.


Ltac Equal_heap :=
     match goal with
        | |-  (?h1 +++ ?h2) = (?h1 +++ ?h3) => apply (equal_tactic_l10 h1 h2 h3); Equal_heap
        | |- ?h1 = ?h1 => auto
	| |- (heap.emp +++ ?h1) = ?h2 => apply (equal_tactic_l7 h1 h2); [Equal_heap]
	| |- (?h1 +++ heap.emp) = ?h2 => apply (equal_tactic_l6 h1 h2); [Equal_heap]
	| |- ?h2 = (heap.emp +++ ?h1)  => symmetry; apply (equal_tactic_l7 h1 h2); [Equal_heap]
	| |- ?h2 = (?h1 +++ heap.emp) => symmetry;apply (equal_tactic_l6 h1 h2); [Equal_heap]
        |  id: ?X = (?x1 +++ ?x2) |- (?X +++ ?x1') = (?Y +++ ?x2') => rewrite id ;  Equal_heap
        |  id: ?Y = (?y1 +++ ?y2) |- (?X +++ ?x1') = (?Y +++ ?x2') => rewrite id ;  Equal_heap
        |  id: ?X = (?x1 +++ ?x2) |- ?X = (?Y +++ ?x2') => rewrite id ;  Equal_heap
        |  id: ?Y = (?y1 +++ ?y2) |- (?X +++ ?x1') = ?Y => rewrite id ;  Equal_heap
        | |- ((?h1 +++ ?h2) +++ ?h3) = ?X => rewrite (equal_tactic_l2' h1 h2 h3); [Equal_heap]
        | |- ?X = ((?h1 +++ ?h2) +++ ?h3)  => rewrite (equal_tactic_l2' h1 h2 h3); [Equal_heap]
        | |- (?h1 +++ ?h2) = (?h3 +++ ?h4) => apply  (equal_tactic_l1 h1 h2 h3 h4); [Disjoint_heap | Equal_heap]  
        | id1: ?h1 = ?h2 |- ?h1 = ?h3 => rewrite id1; Equal_heap
        | id1: ?h1 = ?h2 |- ?h3 = ?h1 => rewrite id1; Equal_heap
     end.

(*
Lemma tactic_test_equal3: forall h h1 h2 h3 h4 h5 h6 h31 h32 h311 h312 h3121 h3122 s,
  h1 # h2 ->
  h = (h1 +++ h2) ->
  h3 # h4 ->
  h2 = (h3 +++ h4) ->
  h5 # h6 -> 
  h4 = (h5 +++ h6) ->
  h31 # h32 ->
  h3 = (h31 +++ h32) ->
  h311 # h312 ->
  h31 = (h311 +++ h312) ->
  h3121 # h3122 -> 
  h312 = (h3121 +++ h3122) ->
  sep.emp s h3122 ->
   h = (h3121 +++ ((((h1 +++ h5) +++ h6) +++ h32) +++ h311)).

intros.
Equal_heap.
*)

(*

Lemma tactic_test_equal2: forall h x0 x2 x4 x5 h1 h2 h3 h4 x x6 x7 x8 x9 h' h'' x11 x10,
	heap.disjoint x0 x2 ->
	h = (heap.union x0 x2) ->
	heap.disjoint x4 x5 ->
	x2 = (heap.union x4 x5) ->
	heap.disjoint h1 h2 ->
	x4 = (heap.union h1 h2) ->
	heap.disjoint x x6 ->
	h1 = (heap.union x x6) ->
	heap.disjoint x7 x8 ->
	x = (heap.union x7 x8) ->
	heap.disjoint x9 heap.emp ->
	x8 = (heap.union x9 heap.emp) ->
	heap.disjoint h3 h4 ->
	h2 = (heap.union h3 h4) ->
	heap.disjoint x10 x11 ->
	h3 = (heap.union x10 x11) ->
	h4 = heap.emp ->
	h''  =
	(heap.union (heap.union x7 (heap.union x6 (heap.union h2 (heap.union x5 x0)))) h') ->
	heap.disjoint  (heap.union x7 (heap.union x6 (heap.union h2 (heap.union x5 x0)))) h' ->
	h2 = (heap.union x10 x11).
intros.
Equal_heap.
Qed.	

Lemma tactic_test_equal: forall h h1 h2 h11 h12 h21 h22 h111 h112 h121 h122 h211 h212 h221 h222 (h3 h4:heap.h),
     heap.disjoint h1 h2 ->
     heap.disjoint h11 h12 ->
     heap.disjoint h21 h22 ->
     heap.disjoint h111 h112 ->
     heap.disjoint h121 h122 ->
     heap.disjoint h211 h212 ->
     heap.disjoint h221 h222 ->
     h = (heap.union h1 h2) ->
     h1 = (heap.union h11 h12) ->
     h2 = (heap.union h21 h22) ->
     h11 = (heap.union h111 h112) ->
     h12 = (heap.union h121 h122) ->
     h21 = (heap.union h211 h212) ->
     h22 = (heap.union h221 h222) ->
     (heap.union h1 h2) = (heap.union (heap.union h21 h12) (heap.union h22 (heap.union h111 h112))).


intros.
Equal_heap.
Qed.


*)
