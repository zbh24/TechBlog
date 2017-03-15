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

Open Local Scope heap_scope.
Open Local Scope sep_scope.

Ltac Simpl_eval := 
  match goal with
    | id: eval ?e ?s = ?P |- _ => simpl in id; generalize id; clear id; Simpl_eval
    | id: ?P = eval ?e ?s |- _ => simpl in id; generalize id; clear id; Simpl_eval
    | |- _ => (intros || idtac); simpl
  end.


Ltac
 Eval_b_hyp h :=
            match goal with
               | h: eval_b ?e ?s = true |- _ => 
                     generalize (expr_b_semantic_good e s); intro eval_b_HypX; inversion_clear eval_b_HypX as [eval_b_HypX1 eval_b_HypX2]; 
                     generalize (eval_b_HypX1 h); clear eval_b_HypX1 eval_b_HypX2;
                     intro eval_b_HypX; simpl in eval_b_HypX; generalize eval_b_HypX; let x := fresh in intro x; clear eval_b_HypX; clear h
            end
with
 Eval_b_goal :=
            match goal with
                |  |-  eval_b ?e ?s = true => 
                     generalize (expr_b_semantic_good e s); intro eval_b_HypX; inversion_clear eval_b_HypX as [eval_b_HypX1 eval_b_HypX2]; 
                     apply (eval_b_HypX2); clear eval_b_HypX1 eval_b_HypX2; simpl
                |  |-  eval_b ?e ?s = false => apply (expr_b_true_negb_false e s); Eval_b_goal
               	| |- _ => idtac
            end
with
 Eval_b_hyp_clean :=
            match goal with
               | id: eval_b ?e ?s = true |- _ => Eval_b_hyp id;  Eval_b_hyp_clean
               | id: eval_b ?e ?s = false |- _ => generalize (expr_b_false_negb_true e s id); clear id; intro; Eval_b_hyp_clean
               | |- _ => idtac
            end
with
 Omega_exprb :=
            (intros || idtac); Eval_b_hyp_clean; Eval_b_goal; (tauto || omega || Simpl_eval; OmegaZ).

(* Frame rule *)


Ltac Frame_rule_pre A :=
      match goal with
             | |- {{?a1 **  A }} ?c {{?Q}} => idtac
             | |- {{ A ** ?a1}} ?c {{?Q}} => rewrite (sep.con_com_equiv A a1)
             | |- {{ (?a1 ** ?a2) ** ?a3}} ?c {{?Q}} => rewrite (sep.con_assoc_equiv a2 a1 a3); Frame_rule_pre A
             | |- {{ ?a1 ** ?a2}} ?c {{?Q}} => rewrite (sep.con_com_equiv a1 a2); Frame_rule_pre A
      end.

Ltac Frame_rule_post A :=
      match goal with
             | |- {{?P}} ?c {{?a1 **  A }} => idtac
             | |- {{?P}} ?c {{ A ** ?a1}} => rewrite (sep.con_com_equiv A a1)
             | |- {{?P}} ?c {{ (?a1 ** ?a2) ** ?a3}} => rewrite (sep.con_assoc_equiv a2 a1 a3); Frame_rule_post A
             | |- {{?P}} ?c {{ ?a1 ** ?a2}} => rewrite (sep.con_com_equiv a1 a2); Frame_rule_post A
      end.

Ltac Frame_rule A := 
                match goal with
                    | |- {{?P}} ?c {{?Q}} => 
                        (Frame_rule_pre  A); (Frame_rule_post A); 
                        eapply frame_rule
                end.



(*
 * Tactic to decompose / compose heap related to separating conjonction 
 *)

(* a cleaning tactic *)
Ltac emp_red := 
	   match goal with
	          | id: sep.emp ?s ?h |- _ => red in id; emp_red
		  | |-_ => idtac
	   end.
	
Ltac Heap_emp_clean :=
     match goal with
       | id: ?h = heap.emp |- _ => subst h; Heap_emp_clean
       | id: sep.emp ?s ?h |- _ => red in id; Heap_emp_clean
       | id: heap.emp = ?h |- _ => subst h; Heap_emp_clean
       | _ => idtac
      end.

Ltac Decompose_sepcon id h1 h2:=
  inversion_clear id as [h1 X]; inversion_clear X as [h2 Y]; decompose [and] Y; clear Y.

Ltac Compose_sepcon id1 id2:=
    exists id1; exists id2; split; [Heap_emp_clean; Disjoint_heap | (split;[Heap_emp_clean; (Equal_heap) | split; idtac])].

Ltac Intro_sepimp id1 id2 := red; intro id1; intro X; inversion_clear X; intro id2; intro.


(* this tactics resolve some simple goals over store_update *)

Ltac Store_update:= simpl;
   match goal with

      | |- TT ?s ?h => red; simpl; auto

      | id: store.lookup ?v ?s = ?p |- store.lookup ?v (store.update ?v' ?p' ?s) = ?p =>
                 rewrite <- store.lookup_update; [simpl; (Omega_exprb || Store_update || auto) |  Var_uneq || (unfold v; unfold v'; Omega_exprb)]

      | |- store.lookup ?v1 (store.update ?v2 ?p ?s) = ?p1 => 
	     	assert (A1: v1 = v2); [
			Omega_exprb |
			subst v1; rewrite store.lookup_update'; auto 
		]
             
      | |- _ => rewrite <- store.lookup_update; [simpl; (Omega_exprb || Store_update || auto || idtac ) |  Var_uneq]
      
      | |- _ => rewrite store.lookup_update'; [simpl; (Omega_exprb || Store_update || auto || idtac )]

      
   end.

(* tactics for cleaning hypothesis *)
Ltac Decompose_hyp := Eval_b_hyp_clean;
  match goal with
    | id: ex ?P |- _ => inversion_clear id; Decompose_hyp
    | id: ?P1 /\ ?P2 |- _ => decompose [and] id; clear id; Decompose_hyp
    | id: eval ?e ?s = ?v |- _ => simpl in id
    | id: (?P1 ** ?P2) ?s ?h |- _ => let h := fresh in (inversion_clear id as [h X]); let h := fresh in (inversion_clear X as [h Y]; decompose [and] Y; clear Y); Decompose_hyp
    | |- _ => idtac
  end.

Ltac Resolve_not_in_var_list_rec :=
  match goal with
    | id: ?v1 = ?v2 \/ ?P |- _ => inversion_clear id;[assert (v1 <> v2); [Var_uneq | contradiction] | Resolve_not_in_var_list_rec]
    | id: False |- _ => contradiction
  end.

Ltac Resolve_not_in_var_list := simpl; red; intros; Resolve_not_in_var_list_rec.


(*
 * tactic to resolve goals of the form: (a |-> b) s h 
 *)

Ltac Mapsto :=
  match goal with 
    | id: (?e1 |-> ?e2) ?s1 ?h |- (?e3 |-> ?e4) ?s2 ?h => apply (mapsto_equiv' s2 s1 h e1 e2 e3 e4 id); [simpl; (Omega_exprb || Store_update || auto)| simpl; (Omega_exprb || Store_update || auto)]
  end.

(*
 * tactics to apply monotony and adjunction
 *)

Ltac assocs_sepcon :=
  match goal with
    | |- ?P -> _  => 
      repeat rewrite sep.con_assoc_equiv
  end.

Ltac rotate_sepcon :=
  match goal with
    | |- ?P -> _ =>
      rewrite sep.con_com_equiv;
	assocs_sepcon
  end.

Ltac try_monotony :=
match goal with
  | |- (?P ** ?PP) ?S ?SS ?M ?H -> (?P ** ?QQ) ?S ?H => 
    apply sep.monotony; split; [intros; auto | intros; idtac]
  | |- ((?L |-> ?V) ** ?PP) ?S ?H -> ((?K |-> ?W) ** ?QQ) ?S ?H => 
    apply sep.monotony; split; [intros; Mapsto | intros; idtac]
  | |- (?P -* ?PP) ?S ?H -> (?Q -* ?QQ) ?S ?H => 
    apply sep.monotony''; [red; intros; Mapsto | red; intros; idtac]
  | |- (?P ** ?PP) ?S ?H -> (?Q ** ?QQ) ?S ?H => 
    rotate_sepcon; try_monotony
end.

Ltac Monotony Hyp :=
  generalize Hyp; clear Hyp; try_monotony.

Ltac Adjunction Hyp :=
  generalize Hyp; clear Hyp; apply sep.adjunction; intros.



