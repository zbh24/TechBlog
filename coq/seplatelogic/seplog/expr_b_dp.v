(*
 *  Seplog is an implementation of separation logic (an extension of Hoare
 *  logic by John C. Reynolds, Peter W. O'Hearn, and colleagues) in the
 *  Coq proof assistant (version 8, http://coq.inria.fr) together with a
 *  sample verification of the heap manager of the Topsy operating system
 *  (version 2, http://www.topsy.net). More information is available at
 *  http://staff.aist.go.jp/reynald.affeldt/seplog/
 *
 *  Copyright (c) 2005, 2006, 2007 Reynald Affeldt and Nicolas Marti
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

(*
  some references:
  http://users.rsise.anu.edu.au/~michaeln/pubs/arith-dp-slides.pdf
  http://www.cse.unsw.edu.au/~cs4161/michaeln-lecture14.pdf
  http://users.rsise.anu.edu.au/~michaeln/pubs/omega-slides.pdf
  http://cs156.stanford.edu/notes/dp-4.pdf
*)

(* 
  The goal of this decision procedure: 
  
  prove that for every environment a system of arithmetic constraint is true
  ==>
  We try to eliminate all the variables, such that to evaluate the system 
  we do not need an environment (and thus this evaluation is the same for 
  every environment)

  Note: in fact we negate the formula of the system and find if 
  for every environment its evaluation is false 
  ( comes from the fact that ~ forall x, P x <-> exists x, ~ P x )

*)

Load seplog_header.

Require Import Bool.
(* we use andb and orb : bool -> bool -> bool *)

(* same as In of the standard library but returning a boolean *)
Fixpoint inb (A:Set) (B:A->A->bool) (l:list A) (a:A) {struct l} : bool :=
  match l with
    nil => false
    | hd :: tl => if B a hd then true else inb A B tl a
  end.
Implicit Arguments inb.

(* add an element to a list only if not already include *)
Fixpoint add_elt_list (A:Set) (B:A->A->bool) (l:list A) (a:A) {struct l} : list A :=
  match l with 
    nil => a :: nil
    | hd :: tl => if B hd a then l else hd :: add_elt_list A B tl a
  end.
Implicit Arguments add_elt_list.

(* append two lists using the previous functions 
   (adding only the elements not already included) *)
Fixpoint app_list (A:Set) (B:A->A->bool) (l1 l2:list A) {struct l1} : list A :=
  match l1 with 
    nil => l2
    | hd :: tl => app_list A B tl (add_elt_list B l2 hd)
  end.
Implicit Arguments app_list.

(* append two option lists *)
Definition option_app (A:Set) (l1 l2:option (list A)) : option (list A) :=
  match l1 with
    None => None
    | Some l1' => match l2 with
                    None => None
                    | Some l2' => Some (l1' ++ l2')
                  end
  end.
Implicit Arguments option_app.

Definition andb_option (a b: option bool) :=
  match a with
    None => None
    | Some a' => match b with
                   None => None
                   | Some b' => Some (andb a' b')
                 end
  end.

Definition orb_option (a b: option bool) :=
  match a with
    None => None
    | Some a' => match b with
                   None => None
                   | Some b' => Some (orb a' b')
                 end
  end.

(****************************************************************************)

(*
 * various additions to expr_b
 *)

(* additional notations for expr_b *)
Notation "e << e'" := (neg_b (ge_b e e')) (at level 78) : sep_scope.
Notation "e <<= e'" := (neg_b (gt_b e e')) (at level 78) : sep_scope.
Notation "! e" := (neg_b e) (at level 78) : sep_scope.
Notation " s '|b=' b " := (eval_b b s = true) (right associativity, at level 80).
Notation " s '|b!=' b " := (eval_b b s = false) (right associativity, at level 80).
Notation " b1 =b> b2 " := ((!b1) ||| b2) (right associativity, at level 80).

(* the list (without redundancies) of free vars of an expr *)
Fixpoint Expr_var (e:expr) {struct e} : list var.v :=
  match e with
    var_e x => x::nil
    | int_e z => nil
    | add_e e1 e2 => app_list beq_nat (Expr_var e1) (Expr_var e2)
    | min_e e1 e2 => app_list beq_nat (Expr_var e1) (Expr_var e2)
    | mul_e e1 e2 => app_list beq_nat (Expr_var e1) (Expr_var e2)
    | div_e e1 e2 => app_list beq_nat (Expr_var e1) (Expr_var e2)
    | mod_e e1 e2 => app_list beq_nat (Expr_var e1) (Expr_var e2)
  end.

(* the list (without redundancies) of free vars of an expr_b *)
Fixpoint Expr_B_var (e:expr_b) : list var.v :=
  match e with 
    true_b => nil
    | eq_b e1 e2 => app_list beq_nat (Expr_var e1) (Expr_var e2)
    | neq_b e1 e2 => app_list beq_nat (Expr_var e1) (Expr_var e2)
    | ge_b e1 e2 => app_list beq_nat (Expr_var e1) (Expr_var e2)
    | gt_b e1 e2 => app_list beq_nat (Expr_var e1) (Expr_var e2)
    | and_b e1 e2 => app_list beq_nat (Expr_B_var e1) (Expr_B_var e2)
    | or_b e1 e2 => app_list beq_nat (Expr_B_var e1) (Expr_B_var e2)
    | neg_b e => Expr_B_var e
  end.

Lemma expr_b_neg_involutive: forall a,
 (forall s, eval_b (!! a) s = eval_b a s).
  intros.
  simpl.
  rewrite negb_elim.
  auto.
Qed.

Lemma eval_b_destruct: forall b s,
 eval_b b s = true \/ eval_b b s = false.
  intros.
  destruct eval_b; auto.
Qed.

Lemma expr_b_eq: forall b1 b2 s,
  ((s |b= b1) <-> (s |b= b2)) -> (eval_b b1 s = eval_b b2 s).
  intros.
  inversion_clear H.
  generalize (eval_b_destruct b1 s); intro X; inversion_clear X.
  generalize (eval_b_destruct b2 s); intro X; inversion_clear X.
  rewrite H; rewrite H2; auto.
  intuition.
  rewrite H3 in H2; discriminate.
  generalize (eval_b_destruct b2 s); intro X; inversion_clear X.
  intuition.
  rewrite H3 in H; discriminate.
  rewrite H; rewrite H2; auto.
Qed.

Lemma expr_b_eq': forall b1 b2 s,
  (eval_b b1 s = eval_b b2 s) -> ((s |b= b1) <-> (s |b= b2)).
  intros.
  split; intros.
  rewrite H in H0.
  auto.
  rewrite <- H in H0.
  auto.
Qed.

(****************************************************************************)

(* Number of constructor in an expr_b formula*)

Fixpoint Expr_B_size (e:expr_b) : nat :=
  match e with 
    true_b => 1
    | eq_b e1 e2 => 1
    | neq_b e1 e2 => 1
    | ge_b e1 e2 => 1
    | gt_b e1 e2 => 1
    | and_b e1 e2 => 1 + (Expr_B_size e1) + (Expr_B_size e2) 
    | or_b e1 e2 => 1 + (Expr_B_size e1) + (Expr_B_size e2)
    | neg_b e => 1 + Expr_B_size e
  end.

(* A lemma asserting that every formula size is greater or equal to 1 *)
Lemma expr_b_min_size: forall b,
  Expr_B_size b >= 1.
  induction b; simpl; intros; try omega.
Qed.

(* We put a formula of expr_b into the disjunctive normal form
   (... /\ ...) \/ (... /\ ...)
   This is perform in three steps:
   1) we propagate negation to final constructor
   2) we translate the bexpr formula into a orlist (data-structure representing a disjunctive normal form), and we replace final (possibly negative) constructor by counter part of form >=
*)

(* step 1: propagation of negation *)
Function neg_propagate (b: expr_b) (n: bool) {struct b} : expr_b :=
  match b with
    | neg_b b1 => neg_propagate b1 (negb n)
    | and_b b1 b2 => if n then (or_b (neg_propagate b1 true) (neg_propagate b2 true)) 
      else (and_b (neg_propagate b1 false) (neg_propagate b2 false))
    | or_b b1 b2 => if n then (and_b (neg_propagate b1 true) (neg_propagate b2 true)) 
      else (or_b (neg_propagate b1 false) (neg_propagate b2 false))
    | _ => if n then (neg_b b) else b
  end.

(* Here is a lemma asserting that a propagation of negation preserve
the semantics of a formula. *)

Lemma neg_propagate_preserve: forall b n,
  (forall s, eval_b (neg_propagate b n) s = eval_b (if n then (neg_b b) else b) s).
  induction b; simpl; intros; auto.
  rewrite IHb.
  destruct n; simpl; auto.
  rewrite negb_involutive; auto.
  destruct n; simpl; rewrite IHb1; rewrite IHb2; simpl; auto.
  rewrite negb_andb; auto.
  destruct n; simpl; rewrite IHb1; rewrite IHb2; simpl; auto.
  rewrite negb_orb; auto.
Qed.

(* we now prove the correctness of the function bneg_propagate. We
first build the predicate is_bneg_propagate, which assert that no
connectives is under a negation *)

Inductive is_neg_propagate : expr_b -> Prop :=

(* atomic boolean expression are valid formulas *)
| true_b_is_neg_propagate: is_neg_propagate true_b
| eq_b_is_neg_propagate: forall e1 e2, is_neg_propagate (eq_b e1 e2)
| neq_b_is_neg_propagate: forall e1 e2, is_neg_propagate (neq_b e1 e2)
| ge_b_is_neg_propagate: forall e1 e2, is_neg_propagate (ge_b e1 e2)
| gt_b_is_neg_propagate: forall e1 e2, is_neg_propagate (gt_b e1 e2)

(* if a boolean expression is negative, its size
must be 1, which means that it is an atomic formula*)
| neg_b_is_neg_propagate: forall e, Expr_B_size e = 1 -> is_neg_propagate (neg_b e)

(* formulas on both size of connective must be valid 
formulas *)
| and_b_is_neg_propagate: forall e1 e2, 
  (is_neg_propagate e1) -> 
  (is_neg_propagate e2) ->
  (is_neg_propagate (and_b e1 e2))

| or_is_neg_propagate: forall e1 e2, 
  (is_neg_propagate e1) -> 
  (is_neg_propagate e2) ->
  (is_neg_propagate (or_b e1 e2)).

(* The correctness lemma *)
Lemma neg_propagate_correct: forall b n,
  is_neg_propagate (neg_propagate b n).
  induction b; simpl; intros.
  destruct n; constructor; auto.
  destruct n; constructor; auto.
  destruct n; constructor; auto.
  destruct n; constructor; auto.
  destruct n; constructor; auto.
  eapply IHb.
  destruct n; constructor; intuition.
  destruct n; constructor; intuition.
Qed.

(* step 2: put in normal disjunctive form *)

(* 
 * definitions of arithmetic constraints and normal forms 
 *)

Definition constraint := expr.

Definition constraint_semantic (c: constraint) : expr_b := (nat_e 0) >>= c.

(* andlists representent conjunction of constraints *)
Definition andlist  := list constraint.

Fixpoint andlist_semantic (l: andlist) : expr_b:=
 match l with
   nil => true_b
   | hd::tl => (constraint_semantic hd) &&& (andlist_semantic tl)
 end.


Definition andlist_plus_andlist (c1 c2: andlist) : andlist :=
  c1 ++ c2.

Lemma andlist_plus_andlist_sem: forall b1 b2,
  (forall s,
    eval_b (andlist_semantic (andlist_plus_andlist b1 b2)) s =
    eval_b (andlist_semantic b1) s && eval_b (andlist_semantic b2) s
  ).
  induction b1; simpl; intros; auto.
  rewrite IHb1.
  apply andb_assoc.
Qed.

Lemma andlist_semantic_app : forall l1 l2 s,
 eval_b (andlist_semantic (l1 ++ l2)) s =
 eval_b ((andlist_semantic l1) &&& (andlist_semantic l2)) s.
  induction l1.
  intuition.
  intros.
  simpl andlist_semantic.
  apply expr_b_eq; split; intros; try Omega_exprb.
  assert (A1: (s |b= constraint_semantic a) /\ s |b= andlist_semantic (l1 ++ l2)).
  split; Omega_exprb.
  inversion_clear A1.
  rewrite IHl1 in H1.
  Omega_exprb.
  cut ((s |b= constraint_semantic a) /\ s |b= andlist_semantic (l1 ++ l2)).
  intros.
  inversion_clear H0.
  Omega_exprb.
  split; try Omega_exprb.
  rewrite IHl1.
  Omega_exprb.
Qed.

(* an orlist is a disjunction of andlists *)
Definition orlist := list andlist.

Fixpoint orlist_semantic (l: orlist) : expr_b:=
 match l with
   nil => ! true_b
   | hd::tl => (andlist_semantic hd) ||| (orlist_semantic tl)
 end.

Definition orlist_plus_orlist (d1 d2: orlist) : orlist :=
  d1 ++ d2.

Lemma orlist_plus_orlist_sem: forall b1 b2,
  (forall s,
    eval_b (orlist_semantic (orlist_plus_orlist b1 b2)) s =
    eval_b (orlist_semantic b1) s || eval_b (orlist_semantic b2) s
  ).
  induction b1; simpl; intros; auto.
  rewrite IHb1.
  apply orb_assoc.
Qed.

Fixpoint andlist_mult_orlist (c: andlist) (d: orlist) {struct d} : orlist :=
  match d with
    | nil => nil
    | hd::tl => orlist_plus_orlist ((andlist_plus_andlist c hd)::nil) (andlist_mult_orlist c tl)
  end.

Lemma andlist_mult_orlist_sem: forall b2 b1,
  (forall s,
    eval_b (orlist_semantic (andlist_mult_orlist b1 b2)) s =
    eval_b (andlist_semantic b1) s &&
    eval_b (orlist_semantic b2) s
  ).
  induction b2; simpl; intros; auto.
  rewrite andb_comm; auto.
  rewrite IHb2.
  rewrite andb_orb_distrib_r.
  rewrite andlist_plus_andlist_sem.
  auto.
Qed.

Fixpoint orlist_mult_orlist (d1 d2: orlist) {struct d1} : orlist :=
  match d1 with
    | nil => nil
    | hd::tl => orlist_plus_orlist (andlist_mult_orlist hd d2) (orlist_mult_orlist tl d2)
  end.

Lemma orlist_mult_orlist_sem: forall b1 b2,
  (forall s,
    eval_b (orlist_semantic (orlist_mult_orlist b1 b2)) s =
    eval_b (orlist_semantic b1) s &&
    eval_b (orlist_semantic b2) s
  ).
  induction b1; simpl; intros; auto.
  rewrite orlist_plus_orlist_sem.
  rewrite IHb1.
  rewrite andb_orb_distrib_l.
  rewrite andlist_mult_orlist_sem.
  auto.
Qed.    

Lemma orlist_semantic_app: forall l1 l2 s,
  l1 <> nil ->
  l2 <> nil ->
  eval_b (orlist_semantic (l1 ++ l2)) s =
  eval_b ((orlist_semantic l1) ||| (orlist_semantic l2)) s.
  induction l1.
  intuition.
  intros.
  destruct l1; simpl orlist_semantic.
  destruct l2; try tauto; simpl andlist_semantic; simpl orlist_semantic.
  apply expr_b_eq; split; intros; Omega_exprb.
  destruct l2; try tauto; simpl andlist_semantic; simpl orlist_semantic.
  simpl orlist_semantic in IHl1.
  assert (a0::l1 <> nil); [red;  intro; discriminate | idtac].
  generalize (IHl1 (a1::l2) s H1 H0); intros.
  generalize (expr_b_eq' _ _ _ H2); clear H2; intros.
  inversion_clear H2.
  eapply expr_b_eq; split; intros.
  clear H4; Eval_b_hyp_clean; inversion_clear H4; Eval_b_goal ; intuition.
  assert (A1 : s |b= andlist_semantic a0 ||| orlist_semantic (l1 ++ a1 :: l2)); [Omega_exprb | generalize (H3 A1); clear H3 A1; intros; Omega_exprb].
  clear H3.
  simpl orlist_semantic in H4.
  Eval_b_hyp_clean; Eval_b_goal.
  assert ( expr_b_sem (andlist_semantic a) s \/ (expr_b_sem (andlist_semantic a0) s \/ (expr_b_sem (orlist_semantic l1) s) \/ expr_b_sem (andlist_semantic a1) s \/ expr_b_sem (orlist_semantic l2) s) ).
  intuition.
  inversion_clear H2; [intuition |
    assert (A1: s |b= (andlist_semantic a0 ||| orlist_semantic l1) ||| (andlist_semantic a1 ||| orlist_semantic l2)); [Omega_exprb | generalize (H4 A1); clear H4 A1; intros; Omega_exprb]
  ].
Qed.

(* the main function of step 2 *)
Fixpoint disj_nf (b: expr_b) : orlist :=
  match b with
    | and_b e1 e2 => 
      orlist_mult_orlist (disj_nf e1) (disj_nf e2)
    | or_b e1 e2 => 
      orlist_plus_orlist (disj_nf e1) (disj_nf e2)      
    | neg_b b1 => 
      match b1 with
        | true_b => ((nat_e 1)::nil)::nil
        | eq_b e1 e2 => ((e1 +e (nat_e 1) -e e2)::nil)::((e2 +e (nat_e 1) -e e1)::nil)::nil
        | neq_b e1 e2 => ((e1 -e e2)::(e2 -e e1)::nil)::nil
        | ge_b e1 e2 => ((e1 +e (nat_e 1) -e e2)::nil)::nil
        | gt_b e1 e2 => ((e1 -e e2)::nil)::nil
        | _ => nil
      end
    | true_b => ((nat_e 0)::nil)::nil
    | eq_b e1 e2 => ((e1 -e e2)::(e2 -e e1)::nil)::nil
    | neq_b e1 e2 => ((e1 +e (nat_e 1) -e e2)::nil)::((e2 +e (nat_e 1) -e e1)::nil)::nil
    | ge_b e1 e2 => ((e2 -e e1)::nil)::nil
    | gt_b e1 e2 => ((e2 +e (nat_e 1) -e e1)::nil)::nil
  end.

(* disj_nf preserve the semantics of neg_propagated formula *)
Lemma disj_nf_preserve: forall b,
  is_neg_propagate b ->  
  (forall s, eval_b (orlist_semantic (disj_nf b)) s = eval_b b s).
  induction b; simpl; intros; auto.
  generalize (Zge_cases 0 (eval e s - eval e0 s)); intros.
  generalize (Zge_cases 0 (eval e0 s - eval e s)); intros.
  generalize (Zeq_bool_true (eval e s) (eval e0 s)); intros.
  generalize (Zeq_bool_false (eval e s) (eval e0 s)); intros.
  destruct (Zge_bool 0 (eval e0 s - eval e s)); destruct (Zge_bool 0 (eval e s - eval e0 s)); destruct (Zeq_bool (eval e s) (eval e0 s)); simpl; auto;
    ( 
      (  
        generalize (proj1 H3  (refl_equal _)); intros; assert (False); [omega | contradiction]
      ) || (
        generalize (H2  (refl_equal _)); intros; assert (False); [omega | contradiction]
      ) ).
  generalize (Zge_cases 0 (eval e s + 1 - eval e0 s)); intros.
  generalize (Zge_cases 0 (eval e0 s + 1 - eval e s)); intros.
  generalize (Zeq_bool_true (eval e s) (eval e0 s)); intros.
  generalize (Zeq_bool_false (eval e s) (eval e0 s)); intros.
  destruct (Zge_bool 0 (eval e0 s + 1 - eval e s)); destruct (Zge_bool 0 (eval e s + 1 - eval e0 s)); destruct (Zeq_bool (eval e s) (eval e0 s)); simpl; auto;
    ( 
      (  
        generalize (proj1 H3  (refl_equal _)); intros; assert (False); [omega | contradiction]
      ) || (
        generalize (H2  (refl_equal _)); intros; assert (False); [omega | contradiction]
      ) ).
  generalize (Zge_cases (eval e s) (eval e0 s)); intros.
  generalize (Zge_cases 0 (eval e0 s - eval e s)); intros.
  destruct (Zge_bool (eval e s) (eval e0 s)); destruct (Zge_bool 0 (eval e0 s - eval e s)); simpl; auto.
  assert (False); [omega | contradiction].
  assert (False); [omega | contradiction].
  generalize (Zgt_cases (eval e s) (eval e0 s)); intros.
  generalize (Zge_cases 0 (eval e0 s + 1 - eval e s)); intros.
  destruct (Zgt_bool (eval e s) (eval e0 s)); destruct (Zge_bool 0 (eval e0 s + 1 - eval e s)); simpl; auto.
  assert (False); [omega | contradiction].
  assert (False); [omega | contradiction].
  destruct b; simpl; auto.
  generalize (Zge_cases 0 (eval e s + 1 - eval e0 s)); intros.
  generalize (Zge_cases 0 (eval e0 s + 1 - eval e s)); intros.
  generalize (Zeq_bool_true (eval e s) (eval e0 s)); intros.
  generalize (Zeq_bool_false (eval e s) (eval e0 s)); intros.
  destruct (Zge_bool 0 (eval e0 s + 1 - eval e s)); destruct (Zge_bool 0 (eval e s + 1 - eval e0 s)); destruct (Zeq_bool (eval e s) (eval e0 s)); simpl; auto;
    ( 
      (  
        generalize (proj1 H3  (refl_equal _)); intros; assert (False); [omega | contradiction]
      ) || (
        generalize (H2  (refl_equal _)); intros; assert (False); [omega | contradiction]
      ) ).
  generalize (Zge_cases 0 (eval e s - eval e0 s)); intros.
  generalize (Zge_cases 0 (eval e0 s - eval e s)); intros.
  generalize (Zeq_bool_true (eval e s) (eval e0 s)); intros.
  generalize (Zeq_bool_false (eval e s) (eval e0 s)); intros.
  destruct (Zge_bool 0 (eval e0 s - eval e s)); destruct (Zge_bool 0 (eval e s - eval e0 s)); destruct (Zeq_bool (eval e s) (eval e0 s)); simpl; auto;
    ( 
      (  
        generalize (proj1 H3  (refl_equal _)); intros; assert (False); [omega | contradiction]
      ) || (
        generalize (H2  (refl_equal _)); intros; assert (False); [omega | contradiction]
      ) ).
  generalize (Zge_cases (eval e s) (eval e0 s)); intros.
  generalize (Zge_cases 0 (eval e s + 1 - eval e0 s)); intros.
  destruct (Zge_bool (eval e s) (eval e0 s)); destruct (Zge_bool 0 (eval e s + 1 - eval e0 s)); simpl; auto.
  assert (False); [omega | contradiction].
  assert (False); [omega | contradiction].
  generalize (Zgt_cases (eval e s) (eval e0 s)); intros.
  generalize (Zge_cases 0 (eval e s - eval e0 s)); intros.
  destruct (Zgt_bool (eval e s) (eval e0 s)); destruct (Zge_bool 0 (eval e s - eval e0 s)); simpl; auto.
  assert (False); [omega | contradiction].
  assert (False); [omega | contradiction].
  inversion_clear H; simpl in H0; generalize (expr_b_min_size b); intros; assert (False); [omega | contradiction].
  inversion_clear H; simpl in H0; generalize (expr_b_min_size b1); generalize (expr_b_min_size b1); intros; assert (False); [omega | contradiction].
  inversion_clear H; simpl in H0; generalize (expr_b_min_size b1); generalize (expr_b_min_size b1); intros; assert (False); [omega | contradiction].
  inversion_clear H.
  rewrite <- (IHb1 H0); rewrite <- (IHb2 H1).
  rewrite orlist_mult_orlist_sem.
  auto.
  inversion_clear H.
  rewrite <- (IHb1 H0); rewrite <- (IHb2 H1).
  rewrite orlist_plus_orlist_sem.
  auto.
Qed.  

(* We compose both step in one *)
Definition expr_b2constraints (b: expr_b) : orlist :=
  disj_nf (neg_propagate b false).

Lemma expr_b2constraints_correct: forall b,
  (forall s, eval_b (orlist_semantic (expr_b2constraints b)) s = eval_b b s).
  intros.
  unfold expr_b2constraints.
  rewrite disj_nf_preserve.
  rewrite neg_propagate_preserve; auto.
  eapply neg_propagate_correct.
Qed.

Open Local Scope Z_scope.

(***********************************)

(* return Some z where z is the value of the expression 
   if this expression is variable free,
   None otherwise *)
Fixpoint expr_compute (e: expr) : option Z :=
   match e with
     var_e x => None
     | int_e x => Some x
     | e1 +e e2 => match expr_compute e1 with
                     None => None
                     | Some e1' => 
                       match expr_compute e2 with
                         None => None
                         | Some e2' => Some (e1' + e2')
                       end
                   end
     | e1 -e e2 => match expr_compute e1 with
                     None => None
                     | Some e1' => 
                       match expr_compute e2 with
                         None => None
                         | Some e2' => Some (e1' - e2')
                       end
                   end
     | e1 *e e2 => match expr_compute e1 with
                     None => 
                     match expr_compute e2 with
                       None => None
                       | Some e2' => if Zeq_bool e2' 0 then Some 0 else None
                     end
                     | Some e1' => 
                       if Zeq_bool e1' 0 then Some 0 else 
                         match expr_compute e2 with
                           None => None
                           | Some e2' => Some (e1' * e2')
                         end
                   end
     | _ => None
   end.

(* if an arithmetic expression can be evaluated without environment, 
   this value is correct *)
Lemma expr_compute_correct: forall e z,
  expr_compute e = Some z ->
  (forall s, eval e s = z).
  induction e; intros; simpl in H; try discriminate; simpl.
  injection H; intros; auto.
  destruct (expr_compute e1); destruct (expr_compute e2); simpl in H; try discriminate; injection H; intros; subst z.
  rewrite (IHe1 z0); auto; rewrite (IHe2 z1); auto.
  destruct (expr_compute e1); destruct (expr_compute e2); simpl in H; try discriminate; injection H; intros; subst z.
  rewrite (IHe1 z0); auto; rewrite (IHe2 z1); auto.
  destruct (expr_compute e1); destruct (expr_compute e2); simpl in H; try discriminate.
  generalize (Zeq_bool_classic z0 0); intro X; inversion_clear X; rewrite H0 in H; injection H; intros; subst z.
  rewrite (IHe1 z0); auto; rewrite (IHe2 z1); auto.
  rewrite (Zeq_bool_true _ _ H0); ring.
  rewrite (IHe1 z0); auto; rewrite (IHe2 z1); auto.
  generalize (Zeq_bool_classic z0 0); intro X; inversion_clear X; rewrite H0 in H; try ((injection H; intros; subst z) || inversion H).
  rewrite (IHe1 z0); auto.
  rewrite (Zeq_bool_true _ _ H0); ring.
  generalize (Zeq_bool_classic z0 0); intro X; inversion_clear X; rewrite H0 in H; try ((injection H; intros; subst z) || inversion H).
  rewrite (IHe2 z0); auto.
  rewrite (Zeq_bool_true _ _ H0); ring.
Qed.

(***********************************)

Fixpoint simpl_expr' (e: expr) : expr :=
  match e with
    | var_e v => var_e v
    | int_e z => int_e z
    | e1 +e e2 =>
      match expr_compute (simpl_expr' e1) with
        | None =>
          match expr_compute (simpl_expr' e2) with
            | None => e
            | Some e2' => 
              if Zeq_bool e2' 0 then e1 else e1 +e (int_e e2')
          end
        | Some e1' => 
          if Zeq_bool e1' 0 then
            (match expr_compute (simpl_expr' e2) with
                | None => e2
                | Some e2' => 
                  if Zeq_bool e2' 0 then int_e 0 else int_e e2'
              end
            ) else (
              match expr_compute (simpl_expr' e2) with
                | None => (int_e e1') +e e2
                | Some e2' => 
                  if Zeq_bool e2' 0 then int_e e1' else int_e (e1' + e2')
              end)
      end
    | e1 -e e2 =>
      match expr_compute (simpl_expr' e1) with
        | None =>
          match expr_compute (simpl_expr' e2) with
            | None => e
            | Some e2' => 
              if Zeq_bool e2' 0 then e1 else e1 -e (int_e e2')
          end
        | Some e1' => 
          if Zeq_bool e1' 0 then
            (match expr_compute (simpl_expr' e2) with
                | None => (int_e 0 -e e2)
                | Some e2' => 
                  if Zeq_bool e2' 0 then int_e 0 else int_e ( - e2')
              end
            ) else (
              match expr_compute (simpl_expr' e2) with
                | None => (int_e e1') -e e2
                | Some e2' => 
                  if Zeq_bool e2' 0 then int_e e1' else int_e (e1' - e2')
              end)
      end
    | e1 *e e2 =>
      match expr_compute (simpl_expr' e1) with
        | None =>
          match expr_compute (simpl_expr' e2) with
            | None => e
            | Some e2' => 
              if Zeq_bool e2' 0 then 
                int_e 0 else 
                  if Zeq_bool e2' 1 then e1 else e1 *e (int_e e2')
          end
        | Some e1' => 
          if Zeq_bool e1' 0 then
            int_e 0 else 
              if Zeq_bool e1' 1 then                
                (match expr_compute (simpl_expr' e2) with
                    | None => e2
                    | Some e2' => 
                      if Zeq_bool e2' 0 then int_e 0 else int_e (e2')
                  end
                ) else 
                (match expr_compute (simpl_expr' e2) with
                    | None => (int_e e1') *e e2
                    | Some e2' => 
                      if Zeq_bool e2' 0 then
                        int_e 0 else 
                          if Zeq_bool e2' 1 then int_e e1' else int_e (e1' * e2')
                  end)
      end
    | _ => e
  end.

Lemma simpl_expr'_correct: forall e s,
  eval e s = eval (simpl_expr' e) s.
  induction e; simpl; auto.
  generalize (expr_compute_correct (simpl_expr' e1)); intros.
  destruct (expr_compute (simpl_expr' e1)).
  generalize (H z (refl_equal _) s); clear H; intros.
  rewrite <- IHe1 in H.
  generalize (Zeq_bool_classic z 0); intro X; inversion_clear X.
  rewrite H0.
  generalize (expr_compute_correct (simpl_expr' e2)); intros.
  destruct (expr_compute (simpl_expr' e2)).
  generalize (H1 z0 (refl_equal _) s); clear H1; intros.
  rewrite <- IHe2 in H1.
  generalize (Zeq_bool_classic z0 0); intro X; inversion_clear X.
  rewrite H2.
  rewrite H; rewrite H1.
  rewrite (Zeq_bool_true _ _ H0); rewrite (Zeq_bool_true _ _ H2); auto.
  rewrite H2.
  rewrite H; rewrite H1.
  rewrite (Zeq_bool_true _ _ H0); auto.
  clear H1.
  rewrite H.
  rewrite (Zeq_bool_true _ _ H0); auto.
  rewrite H0.
  generalize (expr_compute_correct (simpl_expr' e2)); intros.
  destruct (expr_compute (simpl_expr' e2)).
  generalize (H1 z0 (refl_equal _) s); clear H1; intros.
  rewrite <- IHe2 in H1.
  generalize (Zeq_bool_classic z0 0); intro X; inversion_clear X.
  rewrite H2.
  rewrite H; rewrite H1.
  rewrite (Zeq_bool_true _ _ H2); simpl; omega.
  rewrite H2.
  rewrite H; rewrite H1.
  simpl; omega.
  simpl; omega.
  generalize (expr_compute_correct (simpl_expr' e2)); intros.
  destruct (expr_compute (simpl_expr' e2)).
  generalize (H0 z (refl_equal _) s); clear H0; intros.
  rewrite <- IHe2 in H0.
  generalize (Zeq_bool_classic z 0); intro X; inversion_clear X.
  rewrite H1.
  rewrite H0.
  rewrite (Zeq_bool_true _ _ H1); simpl; omega.
  rewrite H1.
  rewrite H0.
  simpl; omega.
  simpl; omega.
  generalize (expr_compute_correct (simpl_expr' e1)); intros.
  destruct (expr_compute (simpl_expr' e1)).
  generalize (H z (refl_equal _) s); clear H; intros.
  rewrite <- IHe1 in H.
  generalize (Zeq_bool_classic z 0); intro X; inversion_clear X.
  rewrite H0.
  generalize (expr_compute_correct (simpl_expr' e2)); intros.
  destruct (expr_compute (simpl_expr' e2)).
  generalize (H1 z0 (refl_equal _) s); clear H1; intros.
  rewrite <- IHe2 in H1.
  generalize (Zeq_bool_classic z0 0); intro X; inversion_clear X.
  rewrite H2.
  rewrite H; rewrite H1.
  rewrite (Zeq_bool_true _ _ H0); rewrite (Zeq_bool_true _ _ H2); auto.
  rewrite H2.
  rewrite H; rewrite H1.
  rewrite (Zeq_bool_true _ _ H0); auto.
  clear H1.
  rewrite H.
  rewrite (Zeq_bool_true _ _ H0); auto.
  rewrite H0.
  generalize (expr_compute_correct (simpl_expr' e2)); intros.
  destruct (expr_compute (simpl_expr' e2)).
  generalize (H1 z0 (refl_equal _) s); clear H1; intros.
  rewrite <- IHe2 in H1.
  generalize (Zeq_bool_classic z0 0); intro X; inversion_clear X.
  rewrite H2.
  rewrite H; rewrite H1.
  rewrite (Zeq_bool_true _ _ H2); simpl; omega.
  rewrite H2.
  rewrite H; rewrite H1.
  simpl; omega.
  simpl; omega.
  generalize (expr_compute_correct (simpl_expr' e2)); intros.
  destruct (expr_compute (simpl_expr' e2)).
  generalize (H0 z (refl_equal _) s); clear H0; intros.
  rewrite <- IHe2 in H0.
  generalize (Zeq_bool_classic z 0); intro X; inversion_clear X.
  rewrite H1.
  rewrite H0.
  rewrite (Zeq_bool_true _ _ H1); simpl; omega.
  rewrite H1.
  rewrite H0.
  simpl; omega.
  simpl; omega.
  generalize (expr_compute_correct (simpl_expr' e1)); intros.
  destruct (expr_compute (simpl_expr' e1)).
  generalize (H z (refl_equal _) s); clear H; intros.
  rewrite <- IHe1 in H.
  generalize (Zeq_bool_classic z 0); intro X; inversion_clear X.
  rewrite H0.
  generalize (expr_compute_correct (simpl_expr' e2)); intros.
  destruct (expr_compute (simpl_expr' e2)).
  generalize (H1 z0 (refl_equal _) s); clear H1; intros.
  rewrite <- IHe2 in H1.
  rewrite H.
  rewrite (Zeq_bool_true _ _ H0); simpl; omega.
  clear H1.
  rewrite H.
  rewrite (Zeq_bool_true _ _ H0); simpl; omega.
  rewrite H0.
  generalize (Zeq_bool_classic z 1); intro X; inversion_clear X.
  rewrite H1.
  generalize (expr_compute_correct (simpl_expr' e2)); intros.
  destruct (expr_compute (simpl_expr' e2)).
  generalize (H2 z0 (refl_equal _) s); clear H2; intros.
  rewrite <- IHe2 in H2.
  generalize (Zeq_bool_classic z0 0); intro X; inversion_clear X.
  rewrite H3.
  rewrite H; rewrite H2.
  rewrite (Zeq_bool_true _ _ H3); simpl; omega.
  rewrite H3.
  rewrite H; rewrite H2.
  rewrite (Zeq_bool_true _ _ H1); simpl eval; omega.
  rewrite H.
  rewrite (Zeq_bool_true _ _ H1); simpl eval; omega.
  rewrite H1.
  generalize (expr_compute_correct (simpl_expr' e2)); intros.
  destruct (expr_compute (simpl_expr' e2)).
  generalize (H2 z0 (refl_equal _) s); clear H2; intros.
  rewrite <- IHe2 in H2.
  generalize (Zeq_bool_classic z0 0); intro X; inversion_clear X.
  rewrite H3.
  rewrite H; rewrite H2.
  rewrite (Zeq_bool_true _ _ H3); simpl; omega.
  rewrite H3.
  generalize (Zeq_bool_classic z0 1); intro X; inversion_clear X.
  rewrite H4.
  rewrite H; rewrite H2.
  rewrite (Zeq_bool_true _ _ H4); simpl; omega.
  rewrite H4.
  simpl.
  rewrite H; rewrite H2; auto.
  clear H2.
  rewrite H; auto.
  clear H.
  generalize (expr_compute_correct (simpl_expr' e2)); intros.
  destruct (expr_compute (simpl_expr' e2)).
  generalize (H z (refl_equal _) s); clear H; intros.
  rewrite <- IHe2 in H.
  generalize (Zeq_bool_classic z 0); intro X; inversion_clear X.
  rewrite H0.
  rewrite H.
  rewrite (Zeq_bool_true _ _ H0); simpl; omega.
  rewrite H0.
  generalize (Zeq_bool_classic z 1); intro X; inversion_clear X.
  rewrite H1.
  rewrite H.
  rewrite (Zeq_bool_true _ _ H1); simpl; omega.
  rewrite H1.
  simpl.
  rewrite H; auto.
  clear H.
  auto.
Qed.

Require Import Max.

Open Local Scope nat_scope.

Fixpoint expr_deep (e: expr) : nat :=
  match e with
    | e1 +e e2 => 1 + (max (expr_deep e1) (expr_deep e2))
    | e1 -e e2 => 1 + (max (expr_deep e1) (expr_deep e2))
    | e1 *e e2 => 1 + (max (expr_deep e1) (expr_deep e2))
    | _ => 1
  end.

Close Local Scope nat_scope.

Fixpoint simpl_expr_fp (e: expr) (n: nat) {struct n} : expr :=
  match n with
    | O => e
    | S n' => 
      match e with
        | var_e v => var_e v
        | int_e z => int_e z
        | e1 +e e2 => simpl_expr' ((simpl_expr_fp e1 n') +e (simpl_expr_fp e2 n'))
        | e1 -e e2 => simpl_expr' ((simpl_expr_fp e1 n') -e (simpl_expr_fp e2 n'))
        | e1 *e e2 => simpl_expr' ((simpl_expr_fp e1 n') *e (simpl_expr_fp e2 n'))
        | _ => e
      end
  end.

Opaque simpl_expr'.

Lemma simpl_expr_fp_corect: forall n e s,
  eval e s = eval (simpl_expr_fp e n) s.
  induction n; simpl; auto.
  destruct e; simpl; auto.
  intros.
  rewrite <- simpl_expr'_correct.
  simpl.
  repeat rewrite <- IHn; auto.
  intros.
  rewrite <- simpl_expr'_correct.
  simpl.
  repeat rewrite <- IHn; auto.
  intros.
  rewrite <- simpl_expr'_correct.
  simpl.
  repeat rewrite <- IHn; auto.
Qed.
  
Definition simpl_expr (e: expr) : expr :=
  simpl_expr_fp e (expr_deep e).

Lemma simpl_expr_corect: forall e s,
  eval e s = eval (simpl_expr e) s.
  unfold simpl_expr.
  intros.
  apply simpl_expr_fp_corect.
Qed.
  
Transparent simpl_expr'.

Fixpoint expr_var_fact' (e:expr) (v:nat) {struct e} : (expr * expr) :=
  match e with
    var_e x => if beq_nat x v then (nat_e 1, nat_e 0) else (nat_e 0, var_e x)
    | int_e x => (nat_e 0, int_e x)
    | e1 +e e2 => match expr_var_fact' e1 v with
                    | (e11, e12) => match expr_var_fact' e2 v with
                                      | (e21,e22) => (e11 +e e21, e12 +e e22)
                          	    end
                  end
    | e1 -e e2 => match expr_var_fact' e1 v with
                    | (e11, e12) => match expr_var_fact' e2 v with
                                     | (e21, e22) => (e11 -e e21, e12 -e e22)
                                   end
                  end
    | e1 *e e2 => match expr_var_fact' e1 v with
                    | (e11, e12) => match expr_var_fact' e2 v with
                                     | (e21, e22) => 
                                       (((e12 *e e21) +e (e11 *e e22)) 
                                         +e 
                                         (var_e v *e (e11 *e e21)),
                                       e12 *e e22)
                                   end
                  end
    | e1 /e e2 => (nat_e 0, e1 /e e2)
    | e1 mode e2 => (nat_e 0, e1 mode e2)
  end.

Lemma expr_var_fact'_correct: forall e v e1 e2,
  expr_var_fact' e v = (e1, e2) ->
  (forall s, eval e s = eval ((var_e v *e e1) +e e2) s).
  induction e; simpl; intros.
  generalize (beq_nat_classic v v0); intro X; inversion_clear X.
  rewrite H0 in H.
  injection H; intros; subst e1 e2.
  simpl.
  rewrite (beq_nat_true _ _ H0); OmegaZ.
  rewrite H0 in H.
  injection H; intros; subst e1 e2.
  Simpl_eval; OmegaZ.
  injection H; intros; subst e1 e2.
  Simpl_eval; OmegaZ.
  generalize (IHe1 v); intros; clear IHe1.
  generalize (IHe2 v); intros; clear IHe2.
  destruct (expr_var_fact' e1 v); destruct (expr_var_fact' e2 v); injection H; intros; subst e0 e3.
  rewrite (H0 e e4); auto; rewrite (H1 e5 e6); auto. 
  simpl; ring.
  generalize (IHe1 v); intros; clear IHe1.
  generalize (IHe2 v); intros; clear IHe2.
  destruct (expr_var_fact' e1 v); destruct (expr_var_fact' e2 v); injection H; intros; subst e0 e3.
  rewrite (H0 e e4); auto; rewrite (H1 e5 e6); auto. 
  simpl; ring.
  generalize (IHe1 v); intros; clear IHe1.
  generalize (IHe2 v); intros; clear IHe2.
  destruct (expr_var_fact' e1 v); destruct (expr_var_fact' e2 v); injection H; intros; subst e0 e3.
  rewrite (H0 e e4); auto; rewrite (H1 e5 e6); auto. 
  simpl; ring.
  injection H; intros; subst e0 e3.
  simpl; ring.
  injection H; intros; subst e0 e3.
  simpl; ring.
Qed.

(* Simplify a constraint for a given list a variables 

  Simplify means that it tries to replace coefficient of 
  variables by a value (evaluation without environment)
*)
Fixpoint simpl_varlist_constraint (c:constraint) (v:list nat) {struct v} : constraint :=
  match v with
    nil => simpl_expr c
    | hd :: tl => 
      match expr_var_fact' c hd with
        | (e1, e2) => 
          simpl_expr ( 
            (simpl_expr (var_e hd *e (simpl_varlist_constraint e1 tl))) 
            +e 
            (simpl_expr (simpl_varlist_constraint e2 tl)) )
      end
  end.

(* an arithmetic expression and its simplification evaluate 
   similarly for every environment *)
Lemma simpl_varlist_constraint_correct: forall v c c',
 simpl_varlist_constraint c v = c' ->
 (forall s, eval c s = eval c' s).
  induction v.
  simpl.
  intros.
  rewrite (simpl_expr_corect); rewrite H; auto.
  simpl; intros.
  generalize (expr_var_fact'_correct c a); intros.
  destruct (expr_var_fact' c a).
  rewrite (H0 _ _ (refl_equal _) s).
  simpl.
  rewrite <- H.
  repeat rewrite <- simpl_expr_corect.
  simpl eval.
  repeat rewrite <- simpl_expr_corect.
  simpl.
  generalize (IHv e0 (simpl_varlist_constraint e0 v)); generalize (IHv e (simpl_varlist_constraint e v)); intros.
  rewrite <- H2; auto.
  rewrite <- H1; auto.
Qed.

Definition simpl_constraint (c:constraint) : constraint :=
  simpl_varlist_constraint c (Expr_var c).

Lemma simpl_constraint_correct: forall c,
  (forall s, eval c s = eval (simpl_constraint c) s).
  intros.
  unfold simpl_constraint.
  eapply simpl_varlist_constraint_correct.
  reflexivity.
Qed.

Fixpoint simpl_expr_b (b:expr_b) : expr_b :=
  match b with 
    | eq_b e1 e2 => eq_b (simpl_constraint e1) (simpl_constraint e2)
    | neq_b e1 e2 => neq_b (simpl_constraint e1) (simpl_constraint e2)
    | ge_b e1 e2 => ge_b (simpl_constraint e1) (simpl_constraint e2)
    | gt_b e1 e2 => gt_b (simpl_constraint e1) (simpl_constraint e2)
    | and_b e1 e2 => and_b (simpl_expr_b e1) (simpl_expr_b e2)
    | or_b e1 e2 => or_b (simpl_expr_b e1) (simpl_expr_b e2)
    | neg_b e => neg_b (simpl_expr_b e)
    | _ => b
  end.

Lemma simpl_expr_b_correct: forall b s,
  eval_b b s = eval_b (simpl_expr_b b) s.
  induction b; simpl; auto; intros.
  repeat rewrite <- simpl_constraint_correct; auto.
  repeat rewrite <- simpl_constraint_correct; auto.
  repeat rewrite <- simpl_constraint_correct; auto.
  repeat rewrite <- simpl_constraint_correct; auto.
  rewrite <- IHb; auto.
  rewrite <- IHb1; rewrite <- IHb2; auto.
  rewrite <- IHb1; rewrite <- IHb2; auto.
Qed.

(* simplification of every constraints of an andlist  *)
Fixpoint simpl_andlist (l:andlist) : andlist :=
  match l with
    nil => nil
    | hd :: tl => simpl_constraint hd :: simpl_andlist tl 
  end.

(* simplification preserves evaluation *)
Lemma simpl_andlist_correct: forall l s,
  eval_b (andlist_semantic l) s = eval_b (andlist_semantic (simpl_andlist l)) s.
  induction l.
  auto.
  simpl andlist_semantic.
  intros.
  apply expr_b_eq; split; intros.
  assert ((s |b= constraint_semantic a) /\ (s |b= andlist_semantic l)).
  split; Omega_exprb.
  clear H; inversion_clear H0.
  cut(
    (s |b= constraint_semantic (simpl_constraint a)) /\
    (s |b= andlist_semantic (simpl_andlist l))
  ).
  intros.
  inversion_clear H0.
  Omega_exprb.
  split.
  simpl.
  rewrite <- simpl_constraint_correct.
  simpl in H; auto.
  rewrite <- IHl.
  auto.
  assert(
    (s |b= constraint_semantic (simpl_constraint a)) /\
    (s |b= andlist_semantic (simpl_andlist l))
  ).
  split; Omega_exprb.
  clear H; inversion_clear H0.
  rewrite <- IHl in H1.
  assert (s |b= constraint_semantic a).
  simpl in H.
  rewrite <- simpl_constraint_correct in H.
  auto.
  Omega_exprb.
Qed.

Fixpoint simpl_orlist (l:orlist) : orlist :=
  match l with
    nil => nil
    | hd :: tl => simpl_andlist hd :: simpl_orlist tl
  end.

Lemma simpl_orlist_correct: forall l s,
  eval_b (orlist_semantic l) s = eval_b (orlist_semantic (simpl_orlist l)) s.
  induction l.
  auto.
  simpl orlist_semantic.
  intros.
  apply expr_b_eq; split; intros.
  assert ((s |b= andlist_semantic a) \/ (s |b= orlist_semantic l)).
  Eval_b_hyp_clean.
  inversion_clear H0.
  left; Omega_exprb.
  right; Omega_exprb.
  inversion_clear H0.
  rewrite simpl_andlist_correct in H1; Omega_exprb.
  rewrite IHl in H1; Omega_exprb.
  assert (
    (s |b= andlist_semantic (simpl_andlist a)) \/
    (s |b= orlist_semantic (simpl_orlist l))
  ).
  Eval_b_hyp_clean.
  inversion_clear H0.
  left; Omega_exprb.
  right; Omega_exprb.
  inversion_clear H0.
  rewrite <- simpl_andlist_correct in H1; Omega_exprb.
  rewrite <- IHl in H1; Omega_exprb.
Qed.

(**********************)

Definition expr_var_fact (e:expr) (v:nat) : expr * expr :=
   match expr_var_fact' e v with
     (e1, e2) => (simpl_constraint e1, simpl_constraint e2)
   end.

Lemma expr_var_fact_correct: forall c v e1 e2,
  expr_var_fact c v = (e1, e2) ->
  (forall s, eval c s = eval ((var_e v *e e1) +e e2) s).
  intros.
  unfold expr_var_fact in H.
  generalize (expr_var_fact'_correct c v); intro.
  destruct (expr_var_fact' c v).
  injection H; clear H; intros; subst e1 e2.
  simpl.
  repeat rewrite <-simpl_constraint_correct.
  rewrite (H0 e e0); auto.
Qed.

(**********************)

(* Variable elimination:
  c1 and c2 are two constraints containing the variable v.
  By calculating the coefficients of v we can compute if the variables can be eliminated
  (for details on the elimination mechanism see the following lemma)
*)
Definition elim_var_constraint (c1 c2:constraint) (v:nat) : constraint :=
  match expr_var_fact c1 v with
    | (e11, e12) => 
      match expr_var_fact c2 v with
        | (e21, e22) => 
          match expr_compute (simpl_constraint e11) with
            | None => simpl_constraint c2
            | Some e11' => 
              match expr_compute (simpl_constraint e21) with
                | None => simpl_constraint c2
                | Some e21' => 
                  if andb (Zlt_bool e11' 0) (Zlt_bool 0 e21') then
                    simpl_constraint ((e21 *e e12) -e (e11 *e e22))
                    else 
                      (if andb (Zlt_bool 0 e11') (Zlt_bool e21' 0) then
                        simpl_constraint ((e11 *e e22) -e (e21 *e e12))
                        else 
                          simpl_constraint c2)
              end   
          end   
      end
   end.

Lemma fourier_motzkin_for_integers: forall a1 b1 a2 b2 x,
 a1 < 0 ->
 0 < a2 ->
 0 >= x * a1 + b1 ->
 0 >= x * a2 + b2 ->
 a1 * b2 >= a2 * b1.
intros.
assert (b1 <= - (x * a1)).
intuition.
assert ((x * a2) <= - b2).
intuition.
assert (b1 * a2 <= - (x * a1) * a2).
intuition.
assert ((x * a2) * -a1 <= - b2 * - a1).
intuition.
assert (x * a2 * - a1 = -(x * a1) * a2).
ring.
rewrite H7 in H6; clear H7.
assert (b1 * a2 <= - b2 * - a1).
intuition.
assert (-b2 * - a1 = a1 * b2).
ring.
rewrite H8 in H7; clear H8.
cutrewrite (a2 * b1 = b1 * a2).
intuition.
intuition.
Qed.

Lemma expr_b_semantic_good' : forall e s,
  eval_b e s = true -> expr_b_sem e s.
  intros.
  generalize (expr_b_semantic_good e s); tauto.
Qed.

(* The two constraints allowing the variables elimination implies the constraint resulting from elimination  *)
Lemma elim_var_constraint_correct: forall c1 c2 v s,
  ((s |b=  (constraint_semantic c1) &&& (constraint_semantic c2)) -> 
    (s |b= (constraint_semantic (elim_var_constraint c1 c2 v)))).
  intros.
  generalize (expr_b_semantic_good' _ _ H); intro X; simpl in X.
  unfold elim_var_constraint.
  generalize (expr_var_fact_correct c1 v); intros.
  generalize (expr_var_fact_correct c2 v); intros.
  destruct (expr_var_fact c1 v); destruct (expr_var_fact c2 v).
  generalize (H0 _ _ (refl_equal (e, e0)) s); clear H0; intro.
  generalize (H1 _ _ (refl_equal (e1, e2)) s); clear H1; intro.
  simpl in H0; simpl in H1.
  generalize (expr_compute_correct (simpl_constraint e)); intros.
  generalize (expr_compute_correct (simpl_constraint e1)); intros.
  destruct (expr_compute (simpl_constraint e)); destruct (expr_compute (simpl_constraint e1)).
  generalize (H2 _ (refl_equal (Some z)) s); clear H2; intro.
  generalize (H3 _ (refl_equal (Some z0)) s); clear H3; intro.
  rewrite <-simpl_constraint_correct in H2.
  rewrite <-simpl_constraint_correct in H3.
  generalize (Zlt_cases z 0); intros.
  generalize (Zlt_cases 0 z0); intros.
  destruct (Zlt_bool z 0); destruct (Zlt_bool 0 z0).
  simpl.
  apply Zge_bool_true'.
  rewrite <-simpl_constraint_correct.
  simpl.
  assert (eval e s * eval e2 s >= eval e1 s * eval e0 s).
  apply fourier_motzkin_for_integers with (store.lookup v s); omega.
  omega.
  assert (Zlt_bool 0 z = false).
  apply Zlt_bool_Prop'.
  omega.
  rewrite H6; clear H6.
  simpl.
  rewrite <-simpl_constraint_correct.
  apply Zge_bool_true'; tauto.
  simpl.
  assert (Zlt_bool z0 0 = false).
  apply Zlt_bool_Prop'; omega.
  rewrite H6; clear H6.
  rewrite andb_comm.
  simpl.
  rewrite <-simpl_constraint_correct.
  apply Zge_bool_true'; tauto.
  simpl.
  generalize (Zlt_cases 0 z); intros.
  generalize (Zlt_cases z0 0); intros.
  destruct (Zlt_bool 0 z); destruct (Zlt_bool z0 0).
  simpl.
  apply Zge_bool_true'.
  rewrite <-simpl_constraint_correct.
  assert (eval e1 s * eval e0 s >= eval e s * eval e2 s).
  apply fourier_motzkin_for_integers with (store.lookup v s); omega.
  simpl.
  omega.
  simpl.
  rewrite <-simpl_constraint_correct.
  apply Zge_bool_true'; tauto.
  simpl.
  rewrite <-simpl_constraint_correct.
  apply Zge_bool_true'; tauto.
  simpl.
  rewrite <-simpl_constraint_correct.
  apply Zge_bool_true'; tauto.
  simpl.
  rewrite <-simpl_constraint_correct.
  apply Zge_bool_true'; tauto.
  simpl.
  rewrite <-simpl_constraint_correct.
  apply Zge_bool_true'; tauto.
  simpl.
  rewrite <-simpl_constraint_correct.
  apply Zge_bool_true'; tauto.
Qed.

(* Given a constraint c, a list a constraint l and a variable v,
  we build the list l' of constraints such that it contains
  i) all the constraint of l where v does not appear
  ii)  all the constraint of l where v appears but cannot be eliminated using c
  iii) all constraint of l were v appear and have been eliminated using c
*)
Fixpoint elim_var_andlist' (c: constraint) (l l':andlist) (v: nat) {struct l} : andlist := 
  match l with
    nil => l'
    | hd :: tl => if inb beq_nat (Expr_var (simpl_constraint hd)) v then
      elim_var_andlist' c tl ((elim_var_constraint c hd v)::l') v
      else
        elim_var_andlist' c tl l' v
  end.

Lemma elim_var_andlist'_correct: forall l l' c v,
  (forall s, (s |b=  (andlist_semantic (c::l ++ l'))) -> 
                s |b=  (andlist_semantic (elim_var_andlist' c l l' v))).
induction l.
simpl andlist_semantic.
intros; Omega_exprb.
simpl andlist_semantic; simpl andlist_semantic in IHl.
intros.
destruct inb.
assert (
(s |b= constraint_semantic c) /\
(s |b= constraint_semantic a) /\
(s |b= andlist_semantic (l++l'))
).
split; try Omega_exprb.
split; try Omega_exprb.
inversion_clear H0.
inversion_clear H2.
rewrite andlist_semantic_app in H3.
apply IHl.
cut(
(s |b= constraint_semantic c) /\
(s |b=  andlist_semantic (l ++ elim_var_constraint c a v :: l'))
).
intros.
inversion_clear H2.
Omega_exprb.
split; try Omega_exprb.
rewrite andlist_semantic_app.
cut(
(s |b=  andlist_semantic l) /\
(s |b=  andlist_semantic (elim_var_constraint c a v :: l'))
).
intro X; inversion_clear X.
Omega_exprb.
split; try Omega_exprb.
simpl andlist_semantic.
cut(
(s |b= constraint_semantic (elim_var_constraint c a v)) /\
(s |b= andlist_semantic l')
).
intro X; inversion_clear X.
Omega_exprb.
split; try Omega_exprb.
apply elim_var_constraint_correct.
Omega_exprb.
apply IHl.
Omega_exprb.
Qed.

(* For a given variable v, find the next constraint containing v, and
use it to eliminate v on the rest of the list *)
Fixpoint elim_var_andlist (l l': andlist) (v: nat) {struct l} : andlist :=
  match l with
    nil => l'
    | hd::tl => if inb beq_nat (Expr_var (simpl_constraint hd)) v then
      elim_var_andlist tl (l' ++ (elim_var_andlist' hd tl nil v)) v
      else
        elim_var_andlist tl (hd::l') v
  end.

Lemma elim_var_andlist_correct: forall l l' v,
  (forall s, (s |b=  (andlist_semantic (l ++ l'))) -> 
                s |b=  (andlist_semantic (elim_var_andlist l l' v))).
induction l.
simpl andlist_semantic.
intuition.
simpl andlist_semantic.
intros.
destruct inb.
apply IHl.
rewrite (andlist_semantic_app).
cut(
(s |b= andlist_semantic l) /\
(s |b= andlist_semantic (l' ++ elim_var_andlist' a l nil v))
).
intros.
inversion_clear H0.
Omega_exprb.
assert(
(s |b= constraint_semantic a) /\
(s |b= andlist_semantic (l ++ l'))
).
split; try Omega_exprb.
split; try Omega_exprb.
inversion_clear H0.
rewrite (andlist_semantic_app) in H2.
Omega_exprb.
inversion_clear H0.
rewrite (andlist_semantic_app).
rewrite (andlist_semantic_app) in H2.
cut (
(s |b= andlist_semantic l') /\
(s |b= andlist_semantic (elim_var_andlist' a l nil v))
).
intro X; inversion_clear X.
Omega_exprb.
split; try Omega_exprb.
apply elim_var_andlist'_correct.
simpl andlist_semantic.
rewrite <- app_nil_end.
Omega_exprb.
apply IHl.
rewrite (andlist_semantic_app).
simpl andlist_semantic.
assert (
(s |b= constraint_semantic a) /\
(s |b=  andlist_semantic (l ++ l'))
).
split; try Omega_exprb.
inversion_clear H0.
rewrite (andlist_semantic_app) in H2.
Omega_exprb.
Qed.

(* elimination of the variable v in the orlist  *)
Fixpoint elim_var_orlist (l: orlist) (v: nat) {struct l} : orlist :=
   match l with
      nil => nil
      | hd::tl => (elim_var_andlist hd nil v)::(elim_var_orlist tl v)
   end.

Lemma elim_var_orlist_correct: forall l v,
  (forall s, eval_b (orlist_semantic l) s = true -> 
               eval_b (orlist_semantic (elim_var_orlist l v)) s = true ).
induction l.
simpl.
intuition.
simpl orlist_semantic.
intros.
assert (
(s |b= andlist_semantic a) \/
(s |b= orlist_semantic l)
).
Eval_b_hyp_clean.
inversion_clear H0.
left; Omega_exprb.
right; Omega_exprb.
rewrite (simpl_orlist_correct) in H0.
cut(
(s |b= andlist_semantic (elim_var_andlist a nil v)) \/
(s |b= orlist_semantic (elim_var_orlist l v))
).
intros.
inversion_clear H1; try Omega_exprb.
inversion_clear H0.
left.
apply elim_var_andlist_correct.
rewrite <- app_nil_end.
auto.
right.
apply IHl.
rewrite <- simpl_orlist_correct in H1.
auto.
Qed.

(* Elimination of a list of variables *)
Fixpoint elim_varlist_orlist (l: orlist) (v: list nat) {struct v} : orlist :=
   match v with
      nil => simpl_orlist l
      | hd::tl => (elim_varlist_orlist (elim_var_orlist l hd) tl)
   end.

Lemma elim_varlist_orlist_correct: forall v l,
 (forall s, eval_b (orlist_semantic l) s = true ->
               eval_b (orlist_semantic (elim_varlist_orlist l v)) s = true).
induction v.
simpl.
intros.
rewrite <- simpl_orlist_correct.
auto.
simpl elim_varlist_orlist.
intros.
apply IHv.
apply elim_var_orlist_correct.
auto.
Qed.

(* boolean evaluation of a constraint without environment  *)
Definition eval_constraint (c : constraint) : option bool :=
   match expr_compute c with
     | Some z => Some (Zge_bool 0 z)
     | _ => None
   end.

(* if possible, evaluation is valid for every environment  *)
Lemma eval_constraint2constraint_semantic: forall c b,
  eval_constraint c = Some b ->
  (forall s, eval_b (constraint_semantic c) s = b).
intros.
generalize (expr_compute_correct c); intros.
unfold eval_constraint in H.
destruct (expr_compute c); try discriminate.
simpl.
injection H; intros; subst b.
rewrite (H0 z); auto.
Qed.

(* evaluation of a not empty andlist without environment *)
Fixpoint eval_andlist' (a: andlist) : option bool :=
  match a with
    nil => Some true
    | hd :: tl => match eval_constraint hd with
                  | Some false => Some false
                    | o => match eval_andlist' tl with
                             | None => None
                             | Some false => Some false
                             | Some true => andb_option o (Some true)
                           end
                end
  end.

(* if evaluation was possible, it holds for every environment *)
Lemma eval_andlist'2andlist_semantic: forall a b,
  eval_andlist' a = Some b ->
  (forall s, eval_b (andlist_semantic a) s = b).
  induction a.
  simpl.
  intros.
  injection H; auto.
  simpl eval_andlist'.
  intros.
  generalize (eval_constraint2constraint_semantic a); intros.
  destruct (eval_constraint a).
  simpl in H0.
  simpl.
  rewrite (H0 b0); auto.
  
  destruct b0.
  simpl.
  destruct (eval_andlist' a0).
  rewrite (IHa b0); auto.
  destruct b0; simpl in H; injection H; intros; auto.
  discriminate.
  simpl; injection H; auto.
  
  simpl.
  destruct (eval_andlist' a0).
  rewrite (IHa b0); auto.
  destruct b0.
  simpl in H; discriminate.
  rewrite andb_b_false.
  injection H; auto.
  discriminate.
Qed.

(* Evaluation of an andlist without environment. If empty => error !Z*)
Definition eval_andlist (a: andlist) : option bool :=
  if beq_nat (length a) 0 then
      None 
  else     
      eval_andlist' a.

(* if the evaluation is possible, it holds for every environment *)
Lemma eval_andlist2andlist_semantic: forall a b,
  eval_andlist a = Some b ->
  (forall s, eval_b (andlist_semantic a) s = b).
intros.
unfold eval_andlist in H.
generalize (beq_nat_classic (length a) 0); intro X; inversion_clear X.
rewrite H0 in H; discriminate.
rewrite H0 in H.
apply eval_andlist'2andlist_semantic; auto.
Qed.

(* Evaluation of a non empty orlist without environment *)
Fixpoint eval_orlist' (o: orlist) : option bool :=
   match o with
     nil => Some false
     | hd :: tl => orb_option (eval_andlist hd) (eval_orlist' tl)
   end.

(* if possible, evaluation holds for every environment *)
Lemma eval_orlist'2orlist_semantic: forall a b,
  eval_orlist' a = Some b ->
  (forall s, eval_b (orlist_semantic a) s = b).
induction a; simpl; intros.
injection H; auto.
generalize ( eval_andlist2andlist_semantic a); intros.
destruct (eval_andlist a); simpl in H; try discriminate.
rewrite (H0 b0); auto.
destruct (eval_orlist' a0); simpl in H; try discriminate.
simpl in H.
lapply (IHa b1); intros.
rewrite H1.
injection H; auto.
auto.
Qed.

(* evaluation of an orlist without environement *)
Definition eval_orlist (a: orlist) : option bool :=
  if beq_nat (length a) 0 then
    None 
    else     
      eval_orlist' a.

(*  if possible, evaluation holds for every environment *)
Lemma eval_orlist2orlist_semantic: forall a b,
  eval_orlist a = Some b ->
  (forall s, eval_b (orlist_semantic a) s = b).
  intros.
  unfold eval_orlist in H.
  generalize (beq_nat_classic (length a) 0); intro X; inversion_clear X.
  rewrite H0 in H; discriminate.
  rewrite H0 in H.
  apply eval_orlist'2orlist_semantic; auto.
Qed.

(* The algorithm is

  i) put the boolean expression in normal form
  ii) elimine all its variables
  iii) evaluate wihtout environment
  iv) return the negation 

*)

Definition expr_b_dp (b: expr_b) : bool :=
  match eval_orlist (elim_varlist_orlist (simpl_orlist (expr_b2constraints (simpl_expr_b (!b)))) (Expr_B_var (simpl_expr_b b))) with
    | None => false
    | Some res => negb res      
  end.

(* if the function result is true then the original expression is true for every environment  *)
Lemma expr_b_dp_correct: forall b,
   expr_b_dp b = true ->
   (forall s, s |b= b).
  intros.
  unfold expr_b_dp in H.
  assert ((s |b= b) \/ (s |b!= b)).
  destruct eval_b.
  left; auto.
  right; auto.
  inversion_clear H0; auto.
  assert (s |b= ! b).
  Omega_exprb.
  clear H1.
  rewrite simpl_expr_b_correct in H0.
  rewrite <- (expr_b2constraints_correct) in H0.
  rewrite simpl_orlist_correct in H0.
  generalize (elim_varlist_orlist_correct (Expr_B_var (simpl_expr_b b)) _ _ H0); intros.
  generalize (eval_orlist2orlist_semantic (elim_varlist_orlist
             (simpl_orlist (expr_b2constraints (simpl_expr_b (!b))))
             (Expr_B_var (simpl_expr_b b)))); intros.
  destruct (eval_orlist
          (elim_varlist_orlist
             (simpl_orlist (expr_b2constraints (simpl_expr_b (!b))))
             (Expr_B_var (simpl_expr_b b)))); try discriminate.
  destruct b0; try discriminate.
  rewrite (H2 false (refl_equal _) s) in H1.
  discriminate.
Qed.

Lemma expr_b_impl_intro: forall b1 b2 s,
  (s |b= b1) ->
  (s |b= (b1 =b> b2)) ->
  (s |b= b2).
  intros.
  Omega_exprb.
Qed.

(****************************************************************************)
(*              FrontEnd Tactics for the expr_b_dp function                 *)
(****************************************************************************)

(* Determine if t is a Coq positive variable *)
Ltac Is_pos_var p :=
  match p with
    xH => false
    | xI ?n => false
    | xO ?n => false
    | _ => true
  end.

(* Determine if t is a Coq Z variable *)
Ltac Is_Z_var t :=
  match t with
    | Z0 => false
    | Zpos ?e  => Is_pos_var e
    | Zneg ?e => Is_pos_var e
    | _ => true
  end.

(* add an element to a list only if not already present *)
Ltac Add_list e l :=
  match l with
    | e::?tl => l
    | ?hd::?tl => let x := Add_list e tl in ( constr:(hd::x) )      
    | (@nil Z) => constr:(e::nil)
  end.

(* concatenate two lists using previous tactics *)
Ltac Concat_list l1 l2 :=
  match l1 with
    | ?hd::?tl => let x:= Add_list hd l2 in ( Concat_list tl x )
    | nil => l2
  end.      

(* Build the list of the Coq variable inside the term t *)
(* Such a list is used as an environment  *)
Ltac Build_env t :=
  match t with
    | (?t1 + ?t2)%Z => 
      let x:= (Build_env t1) in (
        let y:= (Build_env t2) in (Concat_list x y)
      )
    | (?t1 - ?t2)%Z => 
      let x:= (Build_env t1) in (
        let y:= (Build_env t2) in (Concat_list x y)
      )
    | (?t1 * ?t2)%Z => 
      let x:= (Build_env t1) in (
        let y:= (Build_env t2) in (Concat_list x y)
      )
    | (?t1 = ?t2)%Z => 
      let x:= (Build_env t1) in (
        let y:= (Build_env t2) in (Concat_list x y)
      )
    | (?t1 -> ?t2)%Z => 
      let x:= (Build_env t1) in (
        let y:= (Build_env t2) in (Concat_list x y)
      )
    | (?t1 > ?t2)%Z => 
      let x:= (Build_env t1) in (
        let y:= (Build_env t2) in (Concat_list x y)
      )
    | (?t1 < ?t2)%Z => 
      let x:= (Build_env t1) in (
        let y:= (Build_env t2) in (Concat_list x y)
      )
    | (?t1 >= ?t2)%Z => 
      let x:= (Build_env t1) in (
        let y:= (Build_env t2) in (Concat_list x y)
      )
    | (?t1 <= ?t2)%Z => 
      let x:= (Build_env t1) in (
        let y:= (Build_env t2) in (Concat_list x y)
      )
    | (?t1 /\ ?t2)%Z => 
      let x:= (Build_env t1) in (
        let y:= (Build_env t2) in (Concat_list x y)
      )
    | (?t1 \/ ?t2)%Z => 
      let x:= (Build_env t1) in (
        let y:= (Build_env t2) in (Concat_list x y)
      )
    | (?t1 <> ?t2)%Z => 
      let x:= (Build_env t1) in (
        let y:= (Build_env t2) in (Concat_list x y)
      )
    | (~ ?t1)%Z => 
      let x:= (Build_env t1) in (x)
    | _ => 
      let x:=(Is_Z_var t) in (
        match (eval compute in x) with
          true => constr:(t::nil)
          | false => constr:(@nil Z)
        end
        )
  end.

(* find the index c of variable v in l *)
Ltac Find_var v l c :=
  match l with
    | v::?tl => constr:c
    | ?hd::?tl => let x := eval compute in (S c) in Find_var v tl x
    | (@nil Z) => constr:0
  end.

(* return the index of variable v in list l *)
Ltac Get_var_index v l := Find_var v l O.

(* Debug tactic *)
Ltac Print t := assert (t = t).

(* translate a Coq term to an arithmetic expression using a list of variables l *)
Ltac To_expr t l :=
  match t with
    | (?t1 + ?t2)%Z => 
      let x:= (To_expr t1 l) in (
        let y:= (To_expr t2 l) in (
          constr:(x +e y)
        )
      )
    | (?t1 - ?t2)%Z => 
      let x:= (To_expr t1 l) in (
        let y:= (To_expr t2 l) in (
          constr:(x -e y)
        )
      )
    | (?t1 * ?t2)%Z => 
      let x:= (To_expr t1 l) in (
        let y:= (To_expr t2 l) in (
          constr:(x *e y)
        )
      )
    | _ => 
      let x:= Is_Z_var t in (
        match eval compute in x with
          | true => 
            let y:= (Get_var_index t l) in 
             constr:(var_e y)
          | false =>               
             constr:(int_e t)
        end
        )
  end.

(* Translate a Coq term to a boolean expression using a list of variables l *)
Ltac To_expr_b t l :=
  match t with
    | (?t1 = ?t2) =>
      let x := To_expr t1 l in (
        let y := To_expr t2 l in (constr:(x == y))
      )
    | (?t1 > ?t2)%Z =>
      let x := To_expr t1 l in (
        let y := To_expr t2 l in (constr:(x >> y))
      )
    | (?t1 >= ?t2)%Z =>
      let x := To_expr t1 l in (
        let y := To_expr t2 l in (constr:(x >>= y))
      )
    | (?t1 < ?t2)%Z =>
      let x := To_expr t1 l in (
        let y := To_expr t2 l in (constr:(! (x >>= y))) (* TODO: change to << when expr_b is extended with lt constructor *)
      )
    | (?t1 <= ?t2)%Z =>
      let x := To_expr t1 l in (
        let y := To_expr t2 l in (constr:(! (x >> y))) (* TODO: change to << when expr_b is extended with lt constructor *)
      )
    | (?t1 -> ?t2) =>
      let x := To_expr_b t1 l in (
        let y := To_expr_b t2 l in (constr:(x =b> y))
      )
    | (?t1 /\ ?t2) =>
      let x := To_expr_b t1 l in (
        let y := To_expr_b t2 l in (constr:(x &&& y))
      )
    | (?t1 \/ ?t2) =>
      let x := To_expr_b t1 l in (
        let y := To_expr_b t2 l in (constr:(x ||| y))
      )
    | (?t1 <> ?t2) =>
      let x := To_expr_b t1 l in (
        let y := To_expr_b t2 l in (constr:(x =/= y))
      )
    | (~ ?t1) =>
      let x := To_expr_b t1 l in (constr:(! x))
  end.

(* return true if the v element is in l *)
Ltac In_list v l :=
  match l with
    | v::?tl => true
    | ?hd::?tl => In_list v tl
    | (@nil Z) => false
  end.

(* return true if at least one element of l1 is in l2  *)
Ltac In_list_list l1 l2 :=
  match l1 with
    | ?hd::?tl =>
      let x := In_list hd l2 in
        match eval compute in x with
          | true => true
          | false => (In_list_list tl l2)
        end
    | (@nil Z) =>
      false
  end.

Lemma new_cut: forall P Q,
  P -> (P -> Q) -> Q.
  intros; tauto.
Qed.

Ltac new_cut P :=
  match goal with
    | |- ?Q =>
      apply (new_cut P Q)
  end.
   
Fixpoint list2store (l: list Z) {struct l} : store.s :=
   match l with
     | nil => store.emp
     | hd::tl => store.update (length l - 1)%nat hd (list2store tl)
   end.

Lemma lookup_list2store: forall l x,   
   store.lookup x (list2store l) = nth x (rev l) 0%Z.
   unfold var.v.
  induction l.
  simpl.
  intro; rewrite store.lookup_emp; destruct x; simpl; auto.
  simpl; intros.
  cutrewrite (length l - 0 = length l)%nat; try omega. 
  assert ( x = length l \/ x <> length l)%nat.
  omega.
  inversion_clear H.
  subst x.
  rewrite store.lookup_update'.
  rewrite app_nth2.
  rewrite rev_length.
  cutrewrite (length l - length l = 0)%nat; try omega.
  auto.
  rewrite rev_length.
  omega.
  rewrite <- store.lookup_update; auto.
  rewrite IHl.
  assert (x < length l \/ x > length l)%nat; try omega.
  inversion_clear H.
  rewrite app_nth1; auto.
  rewrite rev_length; auto.
  rewrite nth_overflow.
  rewrite nth_overflow.
  auto.
  rewrite length_app.
  rewrite rev_length; simpl; omega.
  rewrite rev_length; simpl; omega.
Qed.

Opaque list2store.

(* expr_b_dp without any seeking to hypothesis *)
Ltac expr_b_dp_decision := 
  (* Introduction of all pertinent hypothesis *)
  match goal with
    | |- ?G =>
      (* l is the environment including all coq variable of the goal *)
      let l := (Build_env G) in (
        (* x is the boolean expression corresponding to the goal with respect to the environement l *)
        let x := (To_expr_b G l) in (
          (* a proof of the goal can be achieve by proving that evaluation of x for l is true  *)
          new_cut (eval_b x (list2store (rev l)) = true); [
            (* To prove the evaluation we use the expr_b_dp function  *)
            eapply expr_b_dp_correct; compute; apply refl_equal
              |
            (* we prove entailement  *)
              let h:= fresh in (
                intro h; let y := fresh in (
                  generalize (proj1 (expr_b_semantic_good x (list2store (rev l))) h); intro y; simpl in y; repeat (rewrite lookup_list2store in y); simpl in y; firstorder
                )
             )
          ]            
        )
      )
  end.

(* generalize and clear the first hypothesis that comport a variable in l and then call expr_b_dp or expr_b_dp_decision*)
Ltac Intro_hyp_var_list l :=
  match goal with
    | id: ?a%Z |- _ =>
      let l' := (Build_env a) in (
        let x := In_list_list l' l in (
          match (eval compute in x) with
            | true => generalize id; clear id; (Expr_b_dp || expr_b_dp_decision)
            | false => fail
          end
        )
      )

    | _ => expr_b_dp_decision
  end
(* call Intro_hyp_var_list with the list of Coq variables present in the goal  *)
with Expr_b_dp :=
  match goal with
    | |- ?G =>
      let l := (Build_env G) in (
        Intro_hyp_var_list l
      )
  end.    

(* try to find a hypothesis that can be prove wrong *)
Ltac Contradiction_b :=
  match goal with
    | id: ?A |- _ =>
      assert (~A); [Expr_b_dp | tauto]
    | _ => fail
  end.

(*

Require Import ROmega.

Goal forall x y z res,
  (res = x /\ x >= y /\ x >= z) -> (res >= x /\ res >= y /\ res >= z).
  do 4 intro.
  expr_b_dp_decision.
  Show Proof.
Qed.

Goal forall x y z res,
  (res = x /\ x >= y /\ x >= z) -> res >= x.
  do 4 intro.
  expr_b_dp_decision.
Qed.

Goal forall x y z res,
  (res = x /\ x >= y /\ x >= z) -> res >= x.
do 4 intro.
(*  romega.*)
expr_b_dp_decision.
  Show Proof.
Qed.

Goal forall x y,
  x = 1 ->
  y = 1 ->
  x = y.
  do 2 intro.
expr_b_dp_decision.
  Show Proof.
Qed.

Lemma t: forall a b,
  (a < b \/ b < a) -> a <> b.
  intros.
Expr_b_dp.
  Show Proof.
Qed.

Lemma t': forall a b c,
  (a > b /\ a < b) -> a=c.
  intros.
  Contradiction_b.
Qed.

Lemma t'':
  1 <= 1.
Expr_b_dp.
Qed.

Definition pp (n: nat) : Z :=
  Z_of_nat n * 66.

Lemma test_omega: forall a b c,
  pp a > b -> b > c -> pp a > c.
  intros.
Expr_b_dp.
Show Proof.
Qed.

Lemma test_expr_b_dp: forall a b c,
  a >= b -> b > c -> a > c.
  intros; Expr_b_dp.
  Show Proof.
Qed.

Lemma test2_omega: forall a b c,
  a < b -> b < c -> a < c.
  intros; omega.
  Show Proof.
Qed.

Lemma test2_expr_b_dp: forall a b c,
  a < b -> b < c -> a < c.
  intros; Expr_b_dp.
  Show Proof.
Qed.

Lemma t1_ring: forall a b,
  (a + b) * (a + b) = a*a + b*b + 2*a*b.
  intros.
  ring.
  Show Proof.
Qed.  

Lemma t1_expr_b_dp: forall a b,
  (a + b) * (a + b) = a*a + b*b + 2*a*b.
  intros; Expr_b_dp.
  Show Proof.
Qed.  

Close Local Scope Z_scope.

*)

























