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
Require Import heap_tactic.
Require Import bipl.

Require Import axiomatic.

Import valandloc.

(* commands of the langage *)

Inductive cmd2 : Set :=
  skip2 : cmd2
  | assign2 : var.v -> expr -> cmd2
  | lookup2 : var.v -> expr -> cmd2
  | mutation2 : expr -> expr -> cmd2
  | test_equal2 : var.v -> expr -> expr -> cmd2
  | test_lt2: var.v -> expr -> expr -> cmd2
  | test_not2: var.v -> var.v -> cmd2
  | test_and2: var.v -> var.v -> var.v -> cmd2
  | test_or2: var.v -> var.v -> var.v -> cmd2
  | while2 : expr -> cmd2 -> cmd2
  | seq2 : cmd2 -> cmd2 -> cmd2
  | ifte2 : expr -> cmd2 -> cmd2 -> cmd2.

Open Local Scope sep_scope.
Open Local Scope heap_scope.

(* states *)

Close Local Scope nat_scope.

Definition state := prod store.s heap.h. 

Open Local Scope nat_scope.

(******************************************************************************)

(** operational semantics *)

Inductive exec2 : option state -> cmd2 -> option state -> Prop :=
  exec_none2 : forall c, exec2 None c None
    
  | exec_skip2:  forall s h,  exec2 (Some (s, h)) skip2 (Some (s, h))
    
  | exec_assign2 : forall s h x e,
    exec2 (Some (s, h)) (assign2 x e) (Some (store.update x (eval e s) s, h))
    
  | exec_lookup2 : forall s h x e p v,
    val2loc (eval e s) = p -> (* the relative integer is cast to a location *)
    heap.lookup p h = Some v -> (* we extract the corresponding cell contents if any *)
    exec2 (Some (s, h)) (lookup2 x  e) (Some (store.update x v s, h))

  | exec_lookup_err2 : forall s h x e p,
    val2loc (eval e s) = p -> 
    heap.lookup p h = None -> (* the corresponding location is not allocated *)
    exec2 (Some (s, h)) (lookup2 x  e) None
    
  | exec_mutation2 : forall s h e e' p v,
    val2loc (eval e s) = p -> (* compute the address *)
    heap.lookup p h = Some v -> (* extract the value (if ever present) *)
    exec2 (Some (s, h)) (mutation2 e e') (Some (s, heap.update p (eval e' s) h))
    
  | exec_mutation_err2 : forall s h e e' p,
    val2loc (eval e s) = p -> (* compute the address *)
    heap.lookup p h = None -> (* if the address is not allocated... *)
    exec2 (Some (s, h)) (mutation2 e e') None
    

  | exec_test2_ok: forall s h v e1 e2,
    (eval e1 s = eval e2 s)%Z ->
    exec2 (Some (s, h)) (test_equal2 v e1 e2) (Some (store.update v 1%Z s, h))

  | exec_test2_nok: forall s h v e1 e2,
    (eval e1 s <> eval e2 s)%Z ->
    exec2 (Some (s, h)) (test_equal2 v e1 e2) (Some (store.update v 0%Z s, h))
    
  | exec_lt2_ok: forall s h v e1 e2,
    (eval e1 s < eval e2 s)%Z ->
    exec2 (Some (s, h)) (test_lt2 v e1 e2) (Some (store.update v 1%Z s, h))

  | exec_lt2_nok: forall s h v e1 e2,
    (eval e1 s >= eval e2 s)%Z ->
    exec2 (Some (s, h)) (test_lt2 v e1 e2) (Some (store.update v 0%Z s, h))

  | exec_not2_ok: forall s h v e,
    (eval (var_e e) s = 0)%Z ->
    exec2 (Some (s, h)) (test_not2 v e) (Some (store.update v 1%Z s, h))

  | exec_not2_nok: forall s h v e,
    (eval (var_e e) s <> 0)%Z ->
    exec2 (Some (s, h)) (test_not2 v e) (Some (store.update v 0%Z s, h))

  | exec_and2_ok: forall s h v e1 e2,
    (eval (var_e e1) s <> 0 /\ eval (var_e e2) s <> 0)%Z ->
    exec2 (Some (s, h)) (test_and2 v e1 e2) (Some (store.update v 1%Z s, h))

  | exec_and2_nok: forall s h v e1 e2,
    (eval (var_e e1) s = 0 \/ eval (var_e e2) s = 0)%Z ->
    exec2 (Some (s, h)) (test_and2 v e1 e2) (Some (store.update v 0%Z s, h))

  | exec_or2_ok: forall s h v e1 e2,
    (eval (var_e e1) s <> 0 \/ eval (var_e e2) s <> 0)%Z ->
    exec2 (Some (s, h)) (test_or2 v e1 e2) (Some (store.update v 1%Z s, h))

  | exec_or2_nok: forall s h v e1 e2,
    (eval (var_e e1) s = 0 /\ eval (var_e e2) s = 0)%Z ->
    exec2 (Some (s, h)) (test_and2 v e1 e2) (Some (store.update v 0%Z s, h))

  | exec_seq2 : forall s s' s'' c d,
    exec2 s c s' -> exec2 s' d s'' -> exec2 s (seq2 c d) s''
    
  | exec_while_true2 : forall s h s' s'' b c,
    (eval b s <> 0)%Z ->
    exec2 (Some (s, h)) c s' ->
    exec2 s' (while2 b c) s'' ->    
    exec2 (Some (s, h)) (while2 b c) s''
    
  | exec_while_false2 : forall s h b c,
    (eval b s = 0)%Z ->
    exec2 (Some (s, h)) (while2 b c) (Some (s, h))
    
  | exec_ifte_true2 : forall b c d s h s',
    (eval b s <> 0)%Z ->
    exec2 (Some (s, h)) c s' ->
    exec2 (Some (s, h)) (ifte2 b c d) s'
    
  | exec_ifte_false2 : forall b c d s h s',
    (eval b s = 0)%Z ->
    exec2 (Some (s, h)) d s' ->
    exec2 (Some (s, h)) (ifte2 b c d) s'.

Axiom trad12_fp: cmd -> var.v -> cmd2.

Definition trad12 (c: cmd) : cmd2 :=
  let x := (modified_cmd_var c) in
    (trad12_fp c 0 ).



