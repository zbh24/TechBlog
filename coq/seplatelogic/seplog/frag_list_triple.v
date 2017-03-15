 (*
  *  Seplog is an implementation of separation logic (an extension of Hoare
  *  logic by John C. Reynolds, Peter W. O'Hearn, and colleagues) in the
  *  Coq proof assistant (version 8, http://coq.inria.fr) together with a
  *  sample verification of the heap manager of the Topsy operating system
  *  (version 2, http://www.topsy.net). More information is available at
  *  http://staff.aist.go.jp/reynald.affeldt/seplog.
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

Load seplog_header.

Require Import Omega.
Require Import Bool.
Require Import frag_list_entail.

Require Import Max.

(* TODO: put in util.v *)
Lemma max_lemma3': forall x1 x2 x3,
  x1 >= x2 /\ x1 >= x3 ->
  x1 >= max x2 x3.
  intros.
  inversion_clear H.
  assert (x2 >= x3 \/ x3 >= x2).
  omega.
  inversion_clear H.
  rewrite max_l; omega.
  rewrite max_r; omega.
Qed.

Ltac Resolve_ge_max :=
  match goal with
    | |- ?x >= max ?y ?z =>
      eapply max_lemma3'; split; [Resolve_ge_max | Resolve_ge_max]
    | |- max ?x ?y >= ?z =>
      eapply max_lemma5; Resolve_ge_max
    | |- max ?x ?y >= ?z =>
      eapply max_lemma6; Resolve_ge_max
    | |- ?x + 1 > ?z =>
      cut (x >= z); [Resolve_ge_max | auto]      
    | _ => omega
  end.

(**************************************************************************)

Inductive wpAssrt : Set :=
| wpElt : Assrt -> wpAssrt
| wpSubst : list (var.v * expr) -> wpAssrt -> wpAssrt
| wpLookup : var.v -> expr -> wpAssrt -> wpAssrt
| wpMutation : expr -> expr -> wpAssrt -> wpAssrt
| wpIf : expr_b -> wpAssrt -> wpAssrt -> wpAssrt.

Fixpoint subst_lst2update_store (l:list (var.v * expr)) (P:assert) {struct l} : assert :=
   match l with
      nil => P
      | (x,e)::tl => subst_lst2update_store tl (update_store2 x e P)
   end.

Lemma subst_lst2update_store_app : forall l2 l1 P s h,
   subst_lst2update_store (l2 ++ l1) P s h ->
   subst_lst2update_store l1 (subst_lst2update_store l2 P) s h.
  induction l2.
  simpl.
  auto.
  induction a; simpl; intros.
  unfold update_store2 in H; unfold update_store2.
  eapply IHl2.
  auto.
Qed.

Lemma subst_lst2update_store' : forall l x v s h P,
    subst_lst2update_store (l ++ (x,v)::nil) P s h ->
    update_store2 x v (subst_lst2update_store l P) s h.
intros.
apply (subst_lst2update_store_app _ _ _ _ _ H).
Qed.

Lemma entails_subst_lst2update_store: forall l P1 P2 s h,
   (P1 ==> P2) ->
   subst_lst2update_store l P1 s h ->
   subst_lst2update_store l P2 s h.
  induction l; simpl; auto.
  induction a; simpl; intros.
  apply IHl with (update_store2 a b P1); auto.
  unfold update_store2.
  red; intros.
  apply H; auto.
Qed.

Lemma subst_lst2update_store_and: forall l P1 P2 s h,
  subst_lst2update_store l (fun s h => P1 s h /\ P2 s h) s h ->
  subst_lst2update_store l P1 s h /\ subst_lst2update_store l P2 s h.
  induction l; simpl; intros; auto.
  induction a; simpl.
  apply IHl; auto.
Qed.

Lemma subst_lst2update_store_and': forall l P1 P2 s h,
  subst_lst2update_store l P1 s h /\ subst_lst2update_store l P2 s h ->
  subst_lst2update_store l (fun s h => P1 s h /\ P2 s h) s h.
  induction l; simpl; intros; auto.
  induction a; simpl.
  apply (IHl _ _ _ _ H).
Qed.

Lemma subst_lst2update_store_imply: forall l P1 P2 s h,
  (subst_lst2update_store l P1 s h -> subst_lst2update_store l P2 s h) ->
  subst_lst2update_store l (fun s h => P1 s h -> P2 s h) s h.
  induction l; simpl; intros; auto.
  induction a; simpl.
  apply (IHl _ _ _ _ H).
Qed.

Lemma subst_lst2update_store_exists: forall l (P: expr -> assert) s h,
  (exists x0, (subst_lst2update_store l (P x0)) s h) ->
  subst_lst2update_store l (fun s h => exists e0, P e0 s h) s h.
  induction l.
  simpl.
  intuition.
  induction a; simpl; intros.
  unfold update_store2 in H.
  generalize (IHl (fun e s h => P e (store.update a (eval b s) s) h) _ _ H); intros.
  unfold update_store2.
  auto.
Qed.

Lemma subst_lst2update_store_sep_con: forall l P1 P2 s h,
   ((fun s h => subst_lst2update_store l P1 s h) ** (fun s h => subst_lst2update_store l P2 s h)) s h ->
   subst_lst2update_store l (P1 ** P2) s h.
  induction l.
  intuition.
  induction a; simpl; intros.
  generalize (IHl _ _ _ _ H); intros.
  eapply entails_subst_lst2update_store with (P1 := update_store2 a b P1 ** update_store2 a b P2).
  red; unfold update_store2; simpl; intros.
  Decompose_sepcon H1 h01 h02.
  Compose_sepcon h01 h02; [auto | auto].
  auto.
Qed.

Lemma subst_lst2update_store_sepimp: forall l P1 P2 s h,
  ((fun s h => subst_lst2update_store l P1 s h) -* (fun s h => subst_lst2update_store l P2 s h)) s h ->
  subst_lst2update_store l (P1 -* P2) s h.
  induction l.
  simpl.
  intros.
  Intro_sepimp h' h''.
  red in H.
  eapply H; [split; [apply H0 | apply H1] | apply H2].
  induction a; simpl; intros.
  generalize (IHl _ _ _ _ H); intros.
  eapply entails_subst_lst2update_store with (update_store2 a b P1 -* update_store2 a b P2); [idtac | auto].
  red; simpl; intros.
  Intro_sepimp h' h''.
  red in H1.
  unfold update_store2 in H1.
  eapply H1; [split; [apply H2 | apply H3] | apply H4].
Qed.

Fixpoint wpAssrt_interp (a: wpAssrt) : assert :=
  match a with
    wpElt a1 => Assrt_interp a1
    | wpSubst l L => subst_lst2update_store l (wpAssrt_interp L)
    | wpLookup x e L => (fun s h => exists e0, (e |-> e0 ** (e |-> e0 -* (update_store2 x e0 (wpAssrt_interp L)))) s h)
    | wpMutation e1 e2 L => (fun s h => exists e0, (e1 |-> e0 ** (e1 |-> e2 -* (wpAssrt_interp L))) s h)
    | wpIf b L1 L2 => (fun s h => (eval_pi b s = true -> wpAssrt_interp L1 s h) /\ 
      (eval_b b s = false -> wpAssrt_interp L2 s h))
  end.

(*
 * definition of substitution functions
 *)

(* substitute "pattern" for "replacement" in "e" *) 
Fixpoint subst_e (e patt repl: expr) {struct e} : expr :=
  match e with
    var_e w => match expr_eq e patt with
                 true => repl
                 | false => e
               end
    | int_e i => match expr_eq e patt with
                   true => repl
                   | false => e
                 end
    | add_e e1 e2 => match expr_eq e patt with
                       true => repl
                       | false => add_e (subst_e e1 patt repl) (subst_e e2 patt repl)
                     end
    | min_e e1 e2 => match expr_eq e patt with
                       true => repl
                       | false => min_e (subst_e e1 patt repl) (subst_e e2 patt repl)
                     end
    | mul_e e1 e2 => match expr_eq e patt with
                       true => repl
                       | false => mul_e (subst_e e1 patt repl) (subst_e e2 patt repl)
                     end
    | div_e e1 e2 => match expr_eq e patt with
                       true => repl
                       | false => div_e (subst_e e1 patt repl) (subst_e e2 patt repl)
                     end
    | mod_e e1 e2 => match expr_eq e patt with
                       true => repl
                       | false => mod_e (subst_e e1 patt repl) (subst_e e2 patt repl)
                     end
  end.

Fixpoint subst_b (e: expr_b) (patt repl: expr) {struct e} : expr_b :=
  match e with
    true_b => true_b
    | f == g => subst_e f patt repl == subst_e g patt repl
    | f =/= g => subst_e f patt repl =/= subst_e g patt repl
    | f >>= g => subst_e f patt repl >>= subst_e g patt repl
    | f >> g => subst_e f patt repl >> subst_e g patt repl
    | f &&& g => (subst_b f patt repl) &&& (subst_b g patt repl)
    | f ||| g => (subst_b f patt repl) ||| (subst_b g patt repl)
    | neg_b e => neg_b (subst_b e patt repl)
  end.  

Fixpoint subst_Sigma (a: Sigma) (x: var.v) (e: expr) {struct a} : Sigma :=
  match a with
    singl e1 e2 => singl (subst_e e1 (var_e x) e) (subst_e e2 (var_e x) e)
    | emp => emp
    | star s1 s2 => star (subst_Sigma s1 x e) (subst_Sigma s2 x e)
    | cell e1 => cell (subst_e e1 (var_e x) e)
    | lst e1 e2 => lst (subst_e e1 (var_e x) e) (subst_e e2 (var_e x) e)
  end.

Definition subst_assrt (a: assrt) (x: var.v) (e: expr): assrt :=
  match a with
    (pi, sigm) => (subst_b pi (var_e x) e, subst_Sigma sigm x e)
  end.

Fixpoint subst_Assrt (a: Assrt) (x: var.v) (e: expr) {struct a}: Assrt :=
  match a with
    nil => nil
    | hd::tl => (subst_assrt hd x e)::(subst_Assrt tl x e)
  end.

Fixpoint subst_e_lst (l: list (var.v * expr)) (e: expr) {struct l}: expr :=
  match l with 
    nil => e
    | (x,e')::tl => subst_e_lst tl (subst_e e (var_e x) e')
  end.

Fixpoint subst_b_lst (l: list (var.v * expr)) (e: expr_b) {struct l}: expr_b :=
   match l with 
       nil => e
       | (x,e')::tl => subst_b_lst tl (subst_b e (var_e x) e')
   end.

Fixpoint subst_assrt_lst (l:list (var.v * expr)) (a:assrt) {struct l} : assrt :=
  match l with 
    nil => a
    | (x,e)::tl => subst_assrt_lst tl (subst_assrt a x e)
  end.

Fixpoint subst_Assrt_lst (l:list (var.v * expr)) (a:Assrt) {struct l} : Assrt :=
  match l with 
    nil => a
    | (x,e)::tl => subst_Assrt_lst tl (subst_Assrt a x e)
  end.

(*
 * properties of substitution functions
 *)

Lemma subst_e2store_update: forall e s x v,
   eval (subst_e e (var_e x) v) s = eval e (store.update x (eval v s) s).
  induction e; simpl; auto.
  intros; generalize (beq_nat_classic v x); intro X; inversion_clear X.
  rewrite H.
  rewrite (beq_nat_true _ _ H).
  rewrite store.lookup_update'; auto.
  rewrite H.
  elim store.lookup_update.
  auto.
  apply beq_nat_false; auto.
  intuition.
  intros; rewrite IHe1; rewrite IHe2; auto.
  intros; rewrite IHe1; rewrite IHe2; auto.
  intros; rewrite IHe1; rewrite IHe2; auto.
  intros; rewrite IHe1; rewrite IHe2; auto.
Qed.

Lemma subst_b2store_update: forall b s x v,
  eval_b (subst_b b (var_e x) v) s = eval_b b (store.update x (eval v s) s).
  induction b; simpl; auto; try (intros; repeat rewrite subst_e2store_update; auto ).
  rewrite IHb; auto.
  rewrite IHb1; rewrite IHb2; auto.
  rewrite IHb1; rewrite IHb2; auto.
Qed.

Lemma subst_e_lst_int_e: forall l v s,
  eval (subst_e_lst l (int_e v)) s =  v.
  induction l.
  intuition.
  induction a; simpl; intros.
  eapply IHl.
Qed.

Lemma subst_Sigma2store_update: forall sigm s h x v,
  Sigma_interp (subst_Sigma sigm x v) s h -> 
  Sigma_interp sigm (store.update x (eval v s) s) h.
  induction sigm; simpl; intros; auto.
  inversion_clear H.
  split.
  Mapsto.
  repeat rewrite <- subst_e2store_update.
  auto.
  repeat rewrite <- subst_e2store_update.
  auto.
  repeat rewrite <- subst_e2store_update.
  auto.
  inversion_clear H.
  split.
  inversion_clear H0.
  
  exists x0.
  Mapsto.
  repeat rewrite <- subst_e2store_update.
  auto.
  repeat rewrite <- subst_e2store_update.
  auto.
  Decompose_sepcon H h1 h2.
  Compose_sepcon h1 h2.
  apply IHsigm1.
  auto.
  apply IHsigm2.
  auto.
  eapply Lst_equiv'.
  apply H.
  repeat rewrite <- subst_e2store_update.
  auto.
  repeat rewrite <- subst_e2store_update.
  auto.
Qed.

Lemma subst_Sigma2store_update': forall sigm s h x v,
  Sigma_interp sigm (store.update x (eval v s) s) h -> 
  Sigma_interp (subst_Sigma sigm x v) s h.
  induction sigm; simpl; intros; auto.
  inversion_clear H.
  split.
  Mapsto.
  repeat rewrite <- subst_e2store_update.
  auto.
  repeat rewrite <- subst_e2store_update.
  auto.
  repeat rewrite subst_e2store_update.
  auto.
  inversion_clear H.
  inversion_clear H0.
  split.  
  exists x0.
  Mapsto.
  repeat rewrite subst_e2store_update.
  auto.
  repeat rewrite subst_e2store_update.
  auto.
  Decompose_sepcon H h1 h2.
  Compose_sepcon h1 h2.
  apply IHsigm1.
  auto.
  apply IHsigm2.
  auto.
  eapply Lst_equiv'.
  apply H.
  repeat rewrite <- subst_e2store_update.
  auto.
  repeat rewrite <- subst_e2store_update.
  auto.
Qed.

Lemma subst_Assert2store_update: forall A s h x v,
  Assrt_interp (subst_Assrt A x v) s h -> 
  Assrt_interp A (store.update x (eval v s) s) h.
  induction A; simpl; auto.
  intros.
  inversion_clear H.
  left.
  destruct a.
  simpl; simpl in H0.
  inversion_clear H0.
  split.
  rewrite <- subst_b2store_update; auto.
  apply subst_Sigma2store_update; auto.
  right.
  apply IHA; auto.
Qed.

Lemma subst_lst2update_store_assrt_interp: forall l s h pi sigm,
  assrt_interp (subst_assrt_lst l (pi, sigm)) s h ->
  subst_lst2update_store l (assrt_interp (pi, sigm)) s h.
  induction l; simpl; intros; auto.
  induction a; simpl.
  generalize (IHl _ _ _ _ H); intro.
  cutrewrite ( (update_store2 a b
        (fun (s0 : store.s) (h0 : heap.h) =>
          eval_pi pi s0 = true /\ Sigma_interp sigm s0 h0)) =
  (assrt_interp (subst_b pi (var_e a) b, subst_Sigma sigm a b))).
  auto.
  unfold update_store2; simpl.
  apply sep.assert_ext.
  split; intros.
  rewrite <- subst_b2store_update in H1.
  split; intuition.
  apply subst_Sigma2store_update'.
  auto.
  rewrite subst_b2store_update in H1.
  split; intuition.
  apply subst_Sigma2store_update.
  auto.
Qed.

Lemma subst_lst2update_store_Assrt_interp: forall l A s h,
  Assrt_interp (subst_Assrt_lst l A) s h ->
  subst_lst2update_store l (Assrt_interp A) s h.
  induction l; simpl; intros; auto.
  induction a; simpl.
  generalize (IHl _ _ _ H); intro.
  eapply entails_subst_lst2update_store; [idtac | eapply H0].
  red; intros.
  unfold update_store2.
  apply subst_Assert2store_update; auto.
Qed.

Lemma subst_lst2update_store_subst_b_lst: forall (b':bool) l b s h,
  subst_lst2update_store l (fun s h => eval_pi b s = b') s h ->
  eval_b (subst_b_lst l b) s = b'.
  induction l; simpl; intros; auto.
  induction a; simpl.
  apply IHl with h.
  unfold update_store2 in H.
  cutrewrite (
    (fun s0 (_ : heap.h) => eval_pi (subst_b b (var_e a) b0) s0 = b') =
    (fun s (_ : heap.h) => eval_pi b (store.update a (eval b0 s) s) = b')
  ).
  auto.
  apply sep.assert_ext.
  split; intros.
  rewrite <- subst_b2store_update; auto.
  rewrite subst_b2store_update; auto.
Qed.


Lemma subst_lst2update_store_mapsto: forall l e1 e2 s h,
  (subst_e_lst l e1 |-> subst_e_lst l e2) s h ->
  subst_lst2update_store l (e1 |-> e2) s h.
  induction l.
  intuition.
  induction a; simpl; intros.
  generalize (IHl _ _ _ _ H); intros; clear H.
  eapply entails_subst_lst2update_store with (P1 := (subst_e e1 (var_e a) b |-> subst_e e2 (var_e a) b)); [idtac | auto].
  red; simpl; intros.
  red in H.
  red; red.
  inversion_clear H.
  inversion_clear H1.
  exists x.
  split.
  rewrite subst_e2store_update in H.
  auto.
  rewrite subst_e2store_update in H2.
  auto.
Qed.

Lemma subst_lst2update_store_mapsto': forall l e1 e2 s h,
   subst_lst2update_store l (e1 |-> e2) s h ->
   (subst_e_lst l e1 |-> subst_e_lst l e2) s h.
  induction l.
  intuition.
  induction a; simpl; intros.
  assert (
    update_store2 a b (e1 |-> e2) = (subst_e e1 (var_e a) b |-> subst_e e2 (var_e a) b)
  ).
  eapply sep.assert_ext.
  red; simpl; split; intros.
  red in H0.
  red in H0.
  inversion_clear H0.
  inversion_clear H1.
  red.
  exists x.
  split.
  rewrite  subst_e2store_update.
  auto.
  rewrite  subst_e2store_update.
  auto.
  red in H0.
  inversion_clear H0.
  inversion_clear H1.
  red.
  red.
  exists x.
  split.
  rewrite <- subst_e2store_update.
  auto.
  rewrite <-  subst_e2store_update.
  auto.
  rewrite H0 in H; clear H0.
  generalize (IHl _ _ _ _ H); intros.
  auto.
Qed.

Lemma subst_lst2update_store_lookup' : forall e x v s,
  exists e', eval e s = eval (subst_e e' (var_e x) v) s.
  intros.
  exists (int_e (eval e s)).
  simpl.
  auto.
Qed.

Lemma subst_lst2update_store_lookup: forall l e1 e2 s h P,
  (exists e0, 
    ((subst_e_lst l e1 |-> e0) ** 
      (subst_e_lst l e1 |-> subst_e_lst l e2 -* subst_lst2update_store l P)) s h) ->
  subst_lst2update_store l (fun s' h' => exists e0, (e1 |-> e0 ** (e1 |-> e2 -* P)) s' h') s h.
  induction l.
  intuition.
  induction a; simpl; intros.
  unfold update_store2 in H.
  unfold update_store2.
  generalize (IHl _ _ _ _ _ H); intros.
  clear H.
  eapply entails_subst_lst2update_store with (P1 := (fun s0 h0 =>
    exists e0,
      (subst_e e1 (var_e a) b |-> e0 **
        (subst_e e1 (var_e a) b |-> subst_e e2 (var_e a) b -*
          (fun s h =>
            P (store.update a (eval b s) s) h))) s0 h0)).
  red; simpl; intros.
  inversion_clear H.
  Decompose_sepcon H1 h01 h02.
  generalize (subst_lst2update_store_lookup' x a b s0); intros.
  inversion_clear H3.
  (* c'est pas le bon trucs => besoin d'un lemme en plus *)
  exists x0.
  Compose_sepcon h01 h02.
  red.
  red in H1.
  inversion_clear H1.
  inversion_clear H3.
  exists x1.
  rewrite subst_e2store_update in H1.
  split; auto.
  rewrite <- subst_e2store_update.
  rewrite H6.
  rewrite H5.
  auto.
  Intro_sepimp h01' h'.
  red in H4.
  assert (h02 # h01' /\ ((subst_e e1 (var_e a) b |-> subst_e e2 (var_e a) b) s0 h01')).
  split; auto.
  red in H6.
  inversion_clear H6.
  inversion_clear H8.
  red.
  exists x1.
  split.
  rewrite  subst_e2store_update.
  auto.
  rewrite  subst_e2store_update.
  auto.
  apply (H4 h01' H8 h' H7).
  auto.
Qed.

(*
 * a module for fresh variables (w.r.t. syntactic constructs)
 *)

Module Type FRESH.

  Parameter fresh_e : var.v -> expr -> Prop.
  
  Parameter fresh_b : var.v -> expr_b -> Prop.
  
  Parameter fresh_Sigma : var.v -> Sigma -> Prop.
  
  Parameter fresh_assrt : var.v -> assrt -> Prop.
  
  Parameter fresh_lst : var.v -> (list (var.v * expr)) -> Prop.
  
  Parameter fresh_wpAssrt : var.v -> wpAssrt -> Prop.

  Parameter fresh_cmd : var.v -> cmd -> Prop.
  
  Parameter fresh_lst_decompose : forall x hd0 hd1 tl, fresh_lst x ((hd0,hd1)::tl) -> 
    fresh_e x hd1 /\ x <> hd0 /\ fresh_lst x tl.
  
  Parameter fresh_e_var_e_neq : forall x y, fresh_e x (var_e y) -> x <> y.
  
  Parameter fresh_e_eval: forall e x v s, fresh_e x e ->
    eval e (store.update x v s) = eval e s.
  
  Parameter fresh_wpAssrt_inde: forall L x , fresh_wpAssrt x L ->
    inde (x::nil) (wpAssrt_interp L).

End FRESH.

Module Fresh <: FRESH.

  Fixpoint var_max_expr (e: expr) : var.v :=
    match e with
      var_e w => w
      | int_e i => 0
      | add_e e1 e2 => max (var_max_expr e1) (var_max_expr e2)
      | min_e e1 e2 => max (var_max_expr e1) (var_max_expr e2)
      | mul_e e1 e2 => max (var_max_expr e1) (var_max_expr e2)
      | div_e e1 e2 => max (var_max_expr e1) (var_max_expr e2)
      | mod_e e1 e2 => max (var_max_expr e1) (var_max_expr e2)
    end.
  
  Fixpoint var_max_expr_b (e: expr_b) : var.v :=
    match e with 
      true_b => 0
      | eq_b e1 e2 => max (var_max_expr e1) (var_max_expr e2)
      | neq_b e1 e2 => max (var_max_expr e1) (var_max_expr e2)
      | ge_b e1 e2 => max (var_max_expr e1) (var_max_expr e2)
      | gt_b e1 e2 => max (var_max_expr e1) (var_max_expr e2)
      | and_b e1 e2 => max (var_max_expr_b e1) (var_max_expr_b e2)
      | or_b e1 e2 => max (var_max_expr_b e1) (var_max_expr_b e2)
      | neg_b e => (var_max_expr_b e)
    end.

  Fixpoint var_max_Sigma (s: Sigma) : var.v :=
    match s with
      singl e1 e2 => max (var_max_expr e1) (var_max_expr e2)
      | emp => 0
      | star s1 s2 => max (var_max_Sigma s1) (var_max_Sigma s2)
      | cell e1 => var_max_expr e1
      | lst e1 e2 => max (var_max_expr e1) (var_max_expr e2)
    end.

  Definition var_max_assrt (a: assrt) : var.v :=
    match a with
      (pi, sigm) => max (var_max_expr_b pi) (var_max_Sigma sigm)
    end.

  Fixpoint var_max_Assrt (a: Assrt) : var.v :=
    match a with
      | nil => 0
      | hd::tl => max (var_max_assrt hd) (var_max_Assrt tl)
    end.

  Fixpoint var_max_lst (l: list (var.v * expr)) : var.v :=
    match l with 
      nil => 0
      | (v,e)::tl => max (max v (var_max_expr e)) (var_max_lst tl)
    end.

  Fixpoint var_max_wpAssrt (a: wpAssrt) : var.v :=
    match a with
      wpElt a1 => var_max_Assrt a1
      | wpSubst l L => max (var_max_lst l) (var_max_wpAssrt L)
      | wpLookup x e L=> max (max x (var_max_expr e)) (var_max_wpAssrt L)
      | wpMutation e1 e2 L => max (max (var_max_expr e1) (var_max_expr e2)) (var_max_wpAssrt L)
      | wpIf b L1 L2 => max (max (var_max_wpAssrt L1) (var_max_wpAssrt L2)) (var_max_expr_b b)
    end.

  Fixpoint var_max_cmd (c: cmd) : var.v :=
    match c with
      skip => 0
      | assign x e => max (var_max_expr e) x
      | lookup x e => max (var_max_expr e) x
      | mutation e1 e2 => max (var_max_expr e1) (var_max_expr e2)
      | malloc x e => max (var_max_expr e) x
      | free e => (var_max_expr e)
      | while b c' => max (var_max_expr_b b) (var_max_cmd c')
      | seq c1 c2 => max (var_max_cmd c1) (var_max_cmd c2)
      | ifte b thendo c1 elsedo c2 => max (max (var_max_cmd c1) (var_max_cmd c2)) (var_max_expr_b b)
    end.

  Definition fresh_e x e := (x > var_max_expr e).
 
  Definition fresh_b x b := (x > var_max_expr_b b).

  Definition fresh_Sigma x s := (x > var_max_Sigma s).

  Definition fresh_assrt x a := (x > var_max_assrt a).

  Definition fresh_Assrt x a := (x > var_max_Assrt a).

  Definition fresh_lst x l := (x > var_max_lst l).

  Definition fresh_wpAssrt x L := (x > var_max_wpAssrt L).

  Definition fresh_cmd x c := (x > var_max_cmd c).

  Lemma fresh_lst_decompose : forall x hd0 hd1 tl, fresh_lst x ((hd0,hd1)::tl) -> fresh_e x hd1 /\ x <> hd0 /\ fresh_lst x tl.
    intros.
    unfold fresh_lst in H.
    simpl in H.
    generalize (max_lemma2 _ _ _ H); intro X; inversion_clear X.
    generalize (max_lemma2 _ _ _ H0); intro X; inversion_clear X.
    unfold fresh_lst.
    unfold fresh_e.
    omega.
  Qed.
  
  Lemma fresh_e_var_e_neq : forall x y, fresh_e x (var_e y) -> x <> y.
    intros.
    red in H.
    simpl in H.
    omega.
  Qed.

  Ltac Max_inf_resolve :=
    Max_inf_clean_hyp; Max_inf_resolve_goal
    with          
    Max_inf_clean_hyp :=
    match goal with
      | id: fresh_e _ _  |- _ =>  red in id; simpl in id; Max_inf_clean_hyp
      | id: fresh_b _ _ |- _ => red in id; simpl in id; Max_inf_clean_hyp
      | id: fresh_Sigma _ _ |- _ => red in id; simpl in id; Max_inf_clean_hyp
      | id: fresh_assrt _ _ |- _ => red in id; simpl in id; Max_inf_clean_hyp
      | id: fresh_Assrt _ _ |- _ => red in id; simpl in id; Max_inf_clean_hyp
      | id: fresh_lst _ _ |- _ => red in id; simpl in id; Max_inf_clean_hyp
      | id: fresh_wpAssrt _ _ |- _ => red in id; simpl in id; Max_inf_clean_hyp
      | id: ?x > max ?y ?z |- _ => 
        generalize (max_lemma2 _ _ _ id); intro X; inversion_clear X; clear id; Max_inf_clean_hyp
      | |- _ =>  idtac
    end
    with
    Max_inf_resolve_goal := 
    match goal with
      | |- fresh_e _ _ => red; simpl; Max_inf_resolve_goal
      | |- fresh_b _ _ => red; simpl; Max_inf_resolve_goal
      | |- fresh_Sigma _ _ => red; simpl; Max_inf_resolve_goal
      | |- fresh_assrt _ _ => red; simpl; Max_inf_resolve_goal
      | |- fresh_Assrt _ _ => red; simpl; Max_inf_resolve_goal
      | |- fresh_lst _ _ => red; simpl; Max_inf_resolve_goal
      | |- fresh_wpAssrt _ _ => red; simpl; Max_inf_resolve_goal
      | |- ?x > max ?y ?z => 
        eapply max_lemma3; split; [Max_inf_resolve_goal | Max_inf_resolve_goal]
      | |- _ => omega || tauto || idtac
    end.
  
  Lemma fresh_e_eval: forall e x v s,
    fresh_e x e ->
    eval e (store.update x v s) = eval e s.
    induction e; simpl; intros; auto.
    rewrite <- store.lookup_update.
    auto.
    red in H.
    simpl in H.
    omega.
    rewrite IHe1; try Max_inf_resolve.
    rewrite IHe2; try Max_inf_resolve.
    rewrite IHe1; try Max_inf_resolve.
    rewrite IHe2; try Max_inf_resolve.
    rewrite IHe1; try Max_inf_resolve.
    rewrite IHe2; try Max_inf_resolve.
    rewrite IHe1; try Max_inf_resolve.
    rewrite IHe2; try Max_inf_resolve.
    rewrite IHe2; try Max_inf_resolve.
    rewrite IHe1; try Max_inf_resolve.
  Qed.

Lemma subst_e_lst_eval_sub1: forall e x v0 e0,
    fresh_e x e ->
    x <> v0 ->
    fresh_e x e0 ->
    fresh_e x (subst_e e (var_e v0) e0).
    induction e.
    simpl; intros.
    destruct (beq_nat v v0).
    Max_inf_resolve.
    Max_inf_resolve.
    simpl.
    intros.
    Max_inf_resolve.
    intros.
    assert (fresh_e x e1).
    Max_inf_resolve.
    assert (fresh_e x e2).
    Max_inf_resolve.
    generalize (IHe1 _ _ _ H2 H0 H1); intros.
    generalize (IHe2 _ _ _ H3 H0 H1); intros.
    Max_inf_resolve.
    intros.
    assert (fresh_e x e1).
    Max_inf_resolve.
    assert (fresh_e x e2).
    Max_inf_resolve.
    generalize (IHe1 _ _ _ H2 H0 H1); intros.
    generalize (IHe2 _ _ _ H3 H0 H1); intros.
    Max_inf_resolve.
    intros.
    assert (fresh_e x e1).
    Max_inf_resolve.
    assert (fresh_e x e2).
    Max_inf_resolve.
    generalize (IHe1 _ _ _ H2 H0 H1); intros.
    generalize (IHe2 _ _ _ H3 H0 H1); intros.
    Max_inf_resolve.
    intros.
    assert (fresh_e x e1).
    Max_inf_resolve.
    assert (fresh_e x e2).
    Max_inf_resolve.
    generalize (IHe1 _ _ _ H2 H0 H1); intros.
    generalize (IHe2 _ _ _ H3 H0 H1); intros.
    Max_inf_resolve.
    intros.
    assert (fresh_e x e1).
    Max_inf_resolve.
    assert (fresh_e x e2).
    Max_inf_resolve.
    generalize (IHe1 _ _ _ H2 H0 H1); intros.
    generalize (IHe2 _ _ _ H3 H0 H1); intros.
    Max_inf_resolve.
Qed.

Lemma subst_e_lst_eval: forall l e x v s,
    fresh_e x e ->
    fresh_lst x l ->   
    eval (subst_e_lst l e) (store.update x v s) = eval (subst_e_lst l e) s.
    induction l; simpl; intros; auto.
    rewrite fresh_e_eval.
    auto.
    Max_inf_resolve.
    destruct a.
    rewrite IHl.
    auto.
    generalize (fresh_lst_decompose _ _ _ _ H0); intros.
    decompose [and] H1; clear H1.
    eapply subst_e_lst_eval_sub1; auto.    
    Max_inf_resolve.
Qed.

  (*
   * relations between freshness predicates and the independence predicate ("inde")
   *)
  
  Lemma fresh_b_inde: forall b x v,
    fresh_b x b ->
    inde (x::nil) (fun s h => eval_b b s = v).
    induction b; simpl; intros; auto.
    red.
    intuition.
    red; intros.
    red in H0.
    split; intros.
    rewrite fresh_e_eval; try Max_inf_resolve.
    rewrite fresh_e_eval; try Max_inf_resolve.
    rewrite fresh_e_eval in H1; try Max_inf_resolve.
    rewrite fresh_e_eval in H1; try Max_inf_resolve.
    red; intros.
    red in H0.
    split; intros.
    rewrite fresh_e_eval; try Max_inf_resolve.
    rewrite fresh_e_eval; try Max_inf_resolve.
    rewrite fresh_e_eval in H1; try Max_inf_resolve.
    rewrite fresh_e_eval in H1; try Max_inf_resolve.
    red; intros.
    red in H0.
    split; intros.
    rewrite fresh_e_eval; try Max_inf_resolve.
    rewrite fresh_e_eval; try Max_inf_resolve.
    rewrite fresh_e_eval in H1; try Max_inf_resolve.
    rewrite fresh_e_eval in H1; try Max_inf_resolve.
    red; intros.
    red in H0.
    split; intros.
    rewrite fresh_e_eval; try Max_inf_resolve.
    rewrite fresh_e_eval; try Max_inf_resolve.
    rewrite fresh_e_eval in H1; try Max_inf_resolve.
    rewrite fresh_e_eval in H1; try Max_inf_resolve.
    red; intros.
    red in H0.
    split; intros.
    symmetry.
    eapply negb_sym.
    generalize (IHb x (negb v) H s h x0 v0 H0); intro X; inversion_clear X.
    eapply H2.
    eapply negb_sym.
    symmetry.
    auto.
    symmetry.
    eapply negb_sym.
    generalize (IHb x (negb v) H s h x0 v0 H0); intro X; inversion_clear X.
    eapply H3.
    eapply negb_sym.
    symmetry.
    auto.

    red; split; intros.
    induction v.
    eapply andb_true_intro.
    assert (true = eval_b b1 s /\ true = eval_b b2 s).
    eapply andb_true_eq.
    auto.
    inversion_clear H2.
    split.
    assert (x > var_max_expr_b b1).
    Max_inf_resolve.
    generalize (IHb1 x true H2 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
    assert (x > var_max_expr_b b2).
    Max_inf_resolve.
    generalize (IHb2 x true H2 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
    generalize (andb_false_elim _ _ H1); intro X; inversion_clear X.
    eapply andb_false_intro1.
    assert (x > var_max_expr_b b1).
    Max_inf_resolve.
    generalize (IHb1 x false H3 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
    eapply andb_false_intro2.
    assert (x > var_max_expr_b b2).
    Max_inf_resolve.
    generalize (IHb2 x false H3 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.

    induction v.
    eapply andb_true_intro.
    assert (true = eval_b b1 (store.update x0 v0 s) /\ true = eval_b b2 (store.update x0 v0 s)).
    eapply andb_true_eq.
    auto.
    inversion_clear H2.
    split.
    assert (x > var_max_expr_b b1).
    Max_inf_resolve.
    generalize (IHb1 x true H2 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
    assert (x > var_max_expr_b b2).
    Max_inf_resolve.
    generalize (IHb2 x true H2 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
    generalize (andb_false_elim _ _ H1); intro X; inversion_clear X.
    eapply andb_false_intro1.
    assert (x > var_max_expr_b b1).
    Max_inf_resolve.
    generalize (IHb1 x false H3 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
    eapply andb_false_intro2.
    assert (x > var_max_expr_b b2).
    Max_inf_resolve.
    generalize (IHb2 x false H3 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.

    simpl; split; intros.
    induction v.
    eapply orb_true_intro.
    generalize (orb_prop _ _ H1); intro X; inversion_clear X.
    left.
    assert (x > var_max_expr_b b1).
    Max_inf_resolve.
    generalize (IHb1 x true H3 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
    right.
    assert (x > var_max_expr_b b2).
    Max_inf_resolve.
    generalize (IHb2 x true H3 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
    generalize (orb_false_elim _ _ H1); intros.
    eapply orb_false_intro.
    assert (x > var_max_expr_b b1).
    Max_inf_resolve.
    generalize (IHb1 x false H3 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
    assert (x > var_max_expr_b b2).
    Max_inf_resolve.
    generalize (IHb2 x false H3 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.

    induction v.
    eapply orb_true_intro.
    generalize (orb_prop _ _ H1); intro X; inversion_clear X.
    left.
    assert (x > var_max_expr_b b1).
    Max_inf_resolve.
    generalize (IHb1 x true H3 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
    right.
    assert (x > var_max_expr_b b2).
    Max_inf_resolve.
    generalize (IHb2 x true H3 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
    generalize (orb_false_elim _ _ H1); intros.
    eapply orb_false_intro.
    assert (x > var_max_expr_b b1).
    Max_inf_resolve.
    generalize (IHb1 x false H3 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
    assert (x > var_max_expr_b b2).
    Max_inf_resolve.
    generalize (IHb2 x false H3 s h x0 v0 H0); intro X; inversion_clear X.
    intuition.
  Qed.

  Lemma var_max_Sigma_inde: forall sigm x ,
    fresh_Sigma x sigm ->
    inde (x::nil) (Sigma_interp sigm).
    induction sigm.
    simpl; red; split; intros.
    inversion_clear H1.
    split.
    red.
    red in H2.
    inversion_clear H2.
    exists x1.
    split.
    rewrite fresh_e_eval.
    intuition.
    simpl in H0.
    Max_inf_resolve.
    rewrite fresh_e_eval.
    intuition.
    simpl in H0.
    Max_inf_resolve.
    rewrite fresh_e_eval.
    intuition.
    simpl in H0.
    Max_inf_resolve.
    inversion_clear H1.
    split.
    red.
    red in H2.
    inversion_clear H2.
    exists x1.
    split.
    rewrite fresh_e_eval in H1.
    intuition.
    simpl in H0.
    Max_inf_resolve.
    inversion_clear H1.
    rewrite fresh_e_eval in H4.
    intuition.
    simpl in H0.
    Max_inf_resolve.
    rewrite fresh_e_eval in H3.
    intuition.
    simpl in H0.
    Max_inf_resolve.
    red; simpl; split; intros.
    inversion_clear H1.
    split.
    inversion_clear H2.
    exists x1.
    red.
    red in H1.
    inversion_clear H1.
    exists x2.
    split.
    rewrite fresh_e_eval.
    intuition.
    Max_inf_resolve.
    rewrite fresh_e_eval.
    intuition.
    Max_inf_resolve.
    rewrite fresh_e_eval.
    intuition.
    Max_inf_resolve.    
    inversion_clear H1.
    split.
    inversion_clear H2.
    exists x1.
    red.
    red in H1.
    inversion_clear H1.
    exists x2.
    rewrite fresh_e_eval in H2.
    rewrite fresh_e_eval in H2.
    split.
    intuition.
    intuition.
    Max_inf_resolve.
    Max_inf_resolve.
    rewrite fresh_e_eval in H3.
    intuition.
    Max_inf_resolve.        
    red; simpl; split; intros.
    red in H1.
    red; auto.
    red in H1.
    red; auto.
    red; simpl; split; intros.
    Decompose_sepcon H1 h1 h2.
    Compose_sepcon h1 h2.
    assert (x > var_max_Sigma sigm1).
    Max_inf_resolve.
    generalize (IHsigm1 x H4 s h1 x0 v H0); intro X; inversion_clear X.
    intuition.
    assert (x > var_max_Sigma sigm2).
    Max_inf_resolve.
    generalize (IHsigm2 x H4 s h2 x0 v H0); intro X; inversion_clear X.
    intuition.
    Decompose_sepcon H1 h1 h2.
    Compose_sepcon h1 h2.
    assert (x > var_max_Sigma sigm1).
    Max_inf_resolve.
    generalize (IHsigm1 x H4 s h1 x0 v H0); intro X; inversion_clear X.
    intuition.
    assert (x > var_max_Sigma sigm2).
    Max_inf_resolve.
    generalize (IHsigm2 x H4 s h2 x0 v H0); intro X; inversion_clear X.
    intuition.
    red; simpl; split; intros.
    red in H.
    simpl in H.
    inversion_clear H0; try contradiction.
    subst x0.
    eapply Lst_equiv'.
    apply H1.
    rewrite fresh_e_eval; auto.
    Max_inf_resolve.
    rewrite fresh_e_eval; auto.
    Max_inf_resolve.
    red in H.
    simpl in H.
    inversion_clear H0; try contradiction.
    subst x0.
    eapply Lst_equiv'.
    apply H1.
    rewrite fresh_e_eval; auto.
    Max_inf_resolve.
    rewrite fresh_e_eval; auto.
    Max_inf_resolve.
Qed.    

  Lemma fresh_assrt_inde: forall a x ,
    fresh_assrt x a ->
    inde (x::nil) (assrt_interp a).
    induction a.
    simpl.
    intros.
    assert (x > var_max_expr_b a).
    Max_inf_resolve.
    assert (x > var_max_Sigma b).
    Max_inf_resolve.
    red; simpl; split; intros.
    inversion_clear H3.
    split.
    generalize (fresh_b_inde a x true H0 s h x0 v H2); intro X; inversion_clear X.
    intuition.
    generalize (var_max_Sigma_inde b x H1 s h x0 v H2); intro X; inversion_clear X.
    intuition.
    inversion_clear H3.
    split.
    generalize (fresh_b_inde a x true H0 s h x0 v H2); intro X; inversion_clear X.
    intuition.
    generalize (var_max_Sigma_inde b x H1 s h x0 v H2); intro X; inversion_clear X.
    intuition.
  Qed.

  Lemma fresh_Assrt_inde: forall a x ,
    fresh_Assrt x a ->
    inde (x::nil) (Assrt_interp a).
    induction a; simpl; intros; auto.
    red in H; red; split; simpl; intros; contradiction.
    red in H.
    simpl in H.
    red; simpl; split; intros.
    inversion_clear H1.
    left.
    assert (fresh_assrt x a).
    red; simpl.
    Max_inf_resolve.
    apply (proj1 (fresh_assrt_inde a x H1 s h x0 v H0) H2).
    inversion_clear H0; try contradiction.
    subst x0.
    right.
    assert (fresh_Assrt x a0).
    red; simpl.
    Max_inf_resolve.
    assert (In x (x::nil)).
    simpl ;auto.
    apply (proj1 (IHa x H0 s h x v H1) H2).
    inversion_clear H1.
    left.
    assert (fresh_assrt x a).
    red; simpl.
    Max_inf_resolve.
    apply (proj2 (fresh_assrt_inde a x H1 s h x0 v H0) H2).
    inversion_clear H0; try contradiction.
    subst x0.
    right.
    assert (fresh_Assrt x a0).
    red; simpl.
    Max_inf_resolve.
    assert (In x (x::nil)).
    simpl ;auto.
    apply (proj2 (IHa x H0 s h x v H1) H2).
Qed.

  Lemma fresh_lst_inde: forall l P x,
    inde (x::nil) P ->
    fresh_lst x l ->
    inde (x::nil) (subst_lst2update_store l P).
    induction l.
    red; simpl; split; intros.
    red in H.
    generalize (H s h x0 v H1); intro X; inversion_clear X.
    intuition.
    red in H.
    generalize (H s h x0 v H1); intro X; inversion_clear X.
    intuition.
    induction a.
    red; simpl; split; intros.
    assert (inde (x::nil) (update_store2 a b P)).
    red; simpl; split; intros.
    red in H4.
    red.
    rewrite fresh_e_eval.
    intuition.
    subst x0 x1.
    rewrite store.update_update.
    red in H.
    assert (In x (x::nil)).
    intuition.
    generalize (H (store.update a (eval b s0) s0) h0 x v0 H1); intro X; inversion_clear X.
    intuition.
    Max_inf_resolve.
    intuition.
    subst x0 x1.
    Max_inf_resolve.
    red in H4.
    red.
    rewrite fresh_e_eval in H4.
    intuition.
    subst x0 x1.
    rewrite store.update_update in H4.
    red in H.
    assert (In x (x::nil)).
    intuition.
    generalize (H (store.update a (eval b s0) s0) h0 x v0 H1); intro X; inversion_clear X.
    intuition.
    Max_inf_resolve.
    intuition.
    subst x0 x1.
    Max_inf_resolve.

    assert (x > var_max_lst l).
    Max_inf_resolve.
    generalize (IHl _ _ H3 H4 s h x0 v H1); intro X; inversion_clear X.
    intuition.
    intuition.
    subst x0.

    assert (inde (x::nil) (update_store2 a b P)).
    red; simpl; split; intros.
    red in H3.
    red.
    rewrite fresh_e_eval.
    intuition.
    subst x0.
    rewrite store.update_update.
    red in H.
    assert (In x (x::nil)).
    intuition.
    generalize (H (store.update a (eval b s0) s0) h0 x v0 H1); intro X; inversion_clear X.
    intuition.
    Max_inf_resolve.
    intuition.
    subst x0.
    Max_inf_resolve.
    red in H3.
    red.
    rewrite fresh_e_eval in H3.
    intuition.
    subst x0.
    rewrite store.update_update in H3.
    red in H.
    assert (In x (x::nil)).
    intuition.
    generalize (H (store.update a (eval b s0) s0) h0 x v0 H1); intro X; inversion_clear X.
    intuition.
    Max_inf_resolve.
    intuition.
    subst x0.
    Max_inf_resolve.
    assert (x > var_max_lst l).
    Max_inf_resolve.
    assert (In x (x::nil)).
    intuition.
    generalize (IHl _ _ H1 H3 s h x v H4); intro X; inversion_clear X.
    intuition.
  Qed.

  Lemma fresh_wpAssrt_inde: forall L x ,
    fresh_wpAssrt x L ->
    inde (x::nil) (wpAssrt_interp L).
    induction L.
    simpl.
    red; simpl; split; intros.
    generalize (fresh_Assrt_inde a x H s h x0 v H0); intros.
    intuition.
    generalize (fresh_Assrt_inde a x H s h x0 v H0); intros.
    intuition.
    red; simpl; split; intros.
    assert (inde (x::nil) (wpAssrt_interp L)).
    eapply IHL.
    Max_inf_resolve.
    assert (x > var_max_lst l).
    Max_inf_resolve.
    generalize (fresh_lst_inde _ _ _ H2 H3 s h x0 v H0); intro X; inversion_clear X.
    intuition.
    assert (inde (x::nil) (wpAssrt_interp L)).
    eapply IHL.
    Max_inf_resolve.
    assert (x > var_max_lst l).
    Max_inf_resolve.
    generalize (fresh_lst_inde _ _ _ H2 H3 s h x0 v H0); intro X; inversion_clear X.
    intuition.
    red; simpl; split; intros.
    inversion_clear H1.

    Decompose_sepcon H2 h1 h2.

    exists (int_e (eval x1 s)).
    Compose_sepcon h1 h2.
    Mapsto.
    rewrite fresh_e_eval.
    auto.
    Max_inf_resolve.
    simpl.
    auto.
    Intro_sepimp h1' h'.
    red in H5.
    assert (h2 # h1' /\ (e |-> x1) s h1').
    split.
    auto.
    Mapsto.
    rewrite fresh_e_eval.
    auto.
    Max_inf_resolve.
    generalize (H5 h1' H8 h' H7); intros.
    red in H9.
    red.
    simpl.
    rewrite store.update_update.
    assert (x > var_max_wpAssrt L).
    Max_inf_resolve.
    generalize (IHL _ H10 (store.update v (eval x1 s) s) h' x0 v0 H0); intro X; inversion_clear X.
    intuition.
    Max_inf_resolve.

    inversion_clear H1.

    Decompose_sepcon H2 h1 h2.

    exists (int_e (eval x1 (store.update x0 v0 s))).
    Compose_sepcon h1 h2.
    Mapsto.
    rewrite fresh_e_eval.
    auto.
    Max_inf_resolve.
    Intro_sepimp h1' h'.
    red in H5.
    assert (h2 # h1' /\ (e |-> x1) (store.update x0 v0 s) h1').
    split.
    auto.
    Mapsto.
    rewrite fresh_e_eval.
    auto.
    Max_inf_resolve.
    generalize (H5 h1' H8 h' H7); intros.
    red in H9.
    red.
    simpl.
    rewrite store.update_update in H9.
    assert (x > var_max_wpAssrt L).
    Max_inf_resolve.
    generalize (IHL _ H10 (store.update v (eval x1 (store.update x0 v0 s)) s) h' x0 v0 H0); intro X; inversion_clear X.
    intuition.
    Max_inf_resolve.
    red; simpl; split; intros.

    inversion_clear H1.
    Decompose_sepcon H2 h1 h2.
    exists (int_e (eval x1 s)).
    Compose_sepcon h1 h2.
    Mapsto.
    rewrite fresh_e_eval.
    auto.
    Max_inf_resolve.
    Intro_sepimp h1' h'.
    red in H5.
    assert (h2 # h1' /\ (e |-> e0) s h1').
    split.
    auto.
    Mapsto.
    rewrite fresh_e_eval.
    auto.
    Max_inf_resolve.
    rewrite fresh_e_eval.
    auto.
    Max_inf_resolve.
    generalize (H5 _ H8 _ H7); intros.
    assert (x > var_max_wpAssrt L).
    Max_inf_resolve.
    generalize (IHL _ H10 s h' x0 v H0); intro X; inversion_clear X.
    intuition.

    inversion_clear H1.
    Decompose_sepcon H2 h1 h2.
    exists (int_e (eval x1 (store.update x0 v s))).
    Compose_sepcon h1 h2.
    Mapsto.
    rewrite fresh_e_eval.
    auto.
    Max_inf_resolve.
    Intro_sepimp h1' h'.
    red in H5.
    assert (h2 # h1' /\ (e |-> e0) (store.update x0 v s) h1').
    split.
    auto.
    Mapsto.
    rewrite fresh_e_eval.
    auto.
    Max_inf_resolve.
    rewrite fresh_e_eval.
    auto.
    Max_inf_resolve.
    generalize (H5 _ H8 _ H7); intros.
    assert (x > var_max_wpAssrt L).
    Max_inf_resolve.
    generalize (IHL _ H10 s h' x0 v H0); intro X; inversion_clear X.
    intuition.
    red; simpl; split; intros.
    inversion_clear H1.
    split.
    intros.
    assert (x > var_max_wpAssrt L1).
    Max_inf_resolve.
    generalize (IHL1 _ H4 s h x0 v H0); intro X; inversion_clear X.
    eapply H5.
    eapply H2.
    assert (x > var_max_expr_b e).
    Max_inf_resolve.
    generalize (fresh_b_inde e x true H7 s h x0 v H0); intro X; inversion_clear X.
    intuition.
    intros.
    assert (x > var_max_wpAssrt L2).
    Max_inf_resolve.
    generalize (IHL2 _ H4 s h x0 v H0); intro X; inversion_clear X.
    eapply H5.
    eapply H3.
    assert (x > var_max_expr_b e).
    Max_inf_resolve.
    generalize (fresh_b_inde e x false H7 s h x0 v H0); intro X; inversion_clear X.
    intuition.
    inversion_clear H1.
    split.
    intros.
    assert (x > var_max_wpAssrt L1).
    Max_inf_resolve.
    generalize (IHL1 _ H4 s h x0 v H0); intro X; inversion_clear X.
    eapply H6.
    eapply H2.
    assert (x > var_max_expr_b e).
    Max_inf_resolve.
    generalize (fresh_b_inde e x true H7 s h x0 v H0); intro X; inversion_clear X.
    intuition.
    intros.
    assert (x > var_max_wpAssrt L2).
    Max_inf_resolve.
    generalize (IHL2 _ H4 s h x0 v H0); intro X; inversion_clear X.
    eapply H6.
    eapply H3.
    assert (x > var_max_expr_b e).
    Max_inf_resolve.
    generalize (fresh_b_inde e x false H7 s h x0 v H0); intro X; inversion_clear X.
    intuition.
  Qed.

End Fresh.

Import Fresh.

Ltac apply_entails_subst_lst2update_store id :=
  match goal with
   | id: subst_lst2update_store ?l ?P' ?s ?h |- subst_lst2update_store ?l ?P ?s ?h =>
                eapply entails_subst_lst2update_store with P'; [red; simpl; intros; idtac | auto]
  end.

Ltac cut_replace_list P :=
   match goal with
     | |- subst_lst2update_store ?l ?P' ?s ?h =>
            cut (subst_lst2update_store l P s h); 
	      [intro cut_replace_listA1; apply_entails_subst_lst2update_store cut_replace_listA1 | idtac]
   end.

Lemma subst_lst2update_store_fresh: forall l x' e s h P,
   fresh_lst x' l ->
   subst_lst2update_store l P (store.update x' (eval e s) s) h ->
   subst_lst2update_store l (fun s' h' => P (store.update x' (eval e s) s') h') s h.
  induction l.
  simpl; intros.
  auto.
  induction a; simpl; intros.
  unfold update_store2.
  unfold update_store2 in H0.
  cut_replace_list (
    fun s' h' => (update_store2 a b P) (store.update x' (eval e s) s') h'
  ).
  unfold update_store2 in H1.
  rewrite store.update_update.
  assert ( eval b (store.update x' (eval e s) s0) = eval b s0 ).
  rewrite fresh_e_eval.
  auto.
  generalize (fresh_lst_decompose _ _ _ _ H); intro.
  intuition.
  rewrite <-H2.
  auto.
  generalize (fresh_lst_decompose _ _ _ _ H); intro.
  intuition.
  eapply IHl.
  generalize (fresh_lst_decompose _ _ _ _ H); intro.
  intuition.
  apply_entails_subst_lst2update_store H0.
  unfold update_store2.
  auto.
Qed.

Lemma subst_lst2update_store_fresh': forall l x' e s h P,
  fresh_lst x' l ->
  subst_lst2update_store l (fun s' h' => P (store.update x' (eval e s) s') h') s h ->
  subst_lst2update_store l P (store.update x' (eval e s) s) h.
  induction l.
  simpl; intros.
  auto.
  induction a; simpl; intros.
  unfold update_store2.
  unfold update_store2 in H0.
  cut_replace_list (
    (update_store2 a b P)
  ).
  unfold update_store2 in H1; auto. 
  eapply IHl.
  generalize (fresh_lst_decompose _ _ _ _ H); intro.
  intuition.
  apply_entails_subst_lst2update_store H0.
  unfold update_store2.
  rewrite store.update_update.
  rewrite fresh_e_eval.
  auto.
  generalize (fresh_lst_decompose _ _ _ _ H); intro.
  intuition.
  generalize (fresh_lst_decompose _ _ _ _ H); intro.
  intuition.
Qed.

Lemma intro_fresh_var' : forall l x x' e s h P,
  fresh_lst x' l ->
  fresh_e x' (var_e x) ->
  inde (x'::nil) P -> 
  subst_lst2update_store l (fun s' h' => P (store.update x (eval (var_e x') s') s') h') (store.update x' (eval e s) s) h ->
  subst_lst2update_store l (fun s' h' => P (store.update x (eval e s) s') h') s h.
  intros.
  cut_replace_list (
    (fun s0 h0 => P (store.update x (eval e s) (store.update x' (eval e s) s0)) h0)
  ).
  rewrite store.update_update in H3.
  red in H1.
  assert (In x' (x'::nil)).
  intuition.
  generalize (H1 (store.update x (eval e s) s0) h0 x' (eval e s) H4); intro X; inversion_clear X.
  intuition.
  generalize (fresh_e_var_e_neq _ _ H0); auto.
  generalize (subst_lst2update_store_fresh l x' e s h _ H H2); intro.
  simpl in H3.
  apply_entails_subst_lst2update_store H3.
  rewrite store.lookup_update' in H4.
  auto.
Qed.

(*
 * replace a substitution (e/x) by two substitutions (x/x')(e/x') with x' fresh
 *)
Lemma intro_fresh_var : forall l x x' e s h L,
   fresh_lst x' l -> fresh_wpAssrt x' L -> fresh_e x' (var_e x) ->
   subst_lst2update_store 
	l (fun s' h' => wpAssrt_interp L (store.update x (eval (var_e x') s') s') h') (store.update x' (eval e s) s) h ->
   subst_lst2update_store 
	l (fun s' h' => wpAssrt_interp L (store.update x (eval e s) s') h') s h.
  intros.
  eapply intro_fresh_var' with x'.
  auto.
  auto.
  eapply fresh_wpAssrt_inde.
  auto.
  auto.
Qed.

Definition triple_fresh (P: assrt) (L: wpAssrt) (x: var.v) : Prop := fresh_assrt x P /\ fresh_wpAssrt x L.

Require Import expr_b_dp.

(*
 * weakest pre-condition generator and its soudness
 *)
  
Fixpoint wp_frag (Q: option wpAssrt) (c: cmd) {struct c}: option wpAssrt :=
  match c with 
    skip => match Q with 
              None => None
              | Some Q' => Some Q'
            end
    | assign v e => match Q with 
                            None => None
                            | Some Q' => Some (wpSubst ((v,e)::nil) Q')
                          end
    | lookup v e => match Q with 
                                 None => None
                                 | Some Q' => Some (wpLookup v e Q')
			       end
    | mutation e1 e2 => match Q with 
                                    None => None
                                    | Some Q' => Some (wpMutation e1 e2 Q')
				  end
    | seq c1 c2 => wp_frag (wp_frag Q c2) c1 
    | ifte b thendo c1 elsedo c2 => match (wp_frag Q c1) with 
                                      None => None
                                      | Some Q1 => match (wp_frag Q c2) with 
                                                     None => None
                                                     | Some Q2 => Some (wpIf b (Q1) (Q2))
                                                   end
                                    end
    | while a c => None
    | malloc v e => None
    | free e => None
  end.

Lemma wp_frag_None_is_None: forall c, wp_frag None c = None.
  induction c; simpl; auto.
  rewrite IHc2.
  auto.
  rewrite IHc1.
  auto.
Qed.

Lemma wp_frag_soudness: forall c Q Q', 
  wp_frag (Some Q) c = Some Q' -> {{ wpAssrt_interp Q' }} c {{ wpAssrt_interp Q }}.
  induction c; simpl; intros.

  injection H; intros; subst Q'.
  apply semax_skip.

  injection H; intros; subst Q'.
  simpl.
  apply semax_assign.
  
  injection H; intros; subst Q'.
  simpl.
  apply semax_lookup_backwards.
  
  injection H; intros; subst Q'.
  simpl.
  apply semax_mutation_backwards.
  
  inversion H.
  
  inversion H.
  
  inversion H.
  
  assert ((exists v, wp_frag (Some Q) c2 = Some v) \/ wp_frag (Some Q) c2 = None).
  elim wp_frag.
  intros; left; exists a.
  auto.
  right; auto.
  inversion_clear H0.
  inversion_clear H1.
  rewrite H0 in H.
  eapply semax_seq with (wpAssrt_interp x).
  eapply IHc1.
  auto.
  eapply IHc2.
  auto.
  rewrite H1 in H.
  rewrite wp_frag_None_is_None in H.
  inversion H.
  
  assert ((exists v, wp_frag (Some Q) c1 = Some v) \/ wp_frag (Some Q) c1 = None).
  elim wp_frag.
  intros; left; exists a.
  auto.
  right; auto.
  inversion_clear H0.
  inversion_clear H1.
  rewrite H0 in H.
  assert ((exists v, wp_frag (Some Q) c2 = Some v) \/ wp_frag (Some Q) c2 = None).
  elim wp_frag.
  intros; left; exists a.
  auto.
  right; auto.
  inversion_clear H1.
  inversion_clear H2.
  rewrite H1 in H.
  injection H; intros; subst Q'; simpl.
  apply semax_ifte.
  apply semax_strengthen_pre with (wpAssrt_interp x).
  red.
  tauto.
  eapply IHc1.
  auto.
  apply semax_strengthen_pre with (wpAssrt_interp x0).
  red.
  tauto.
  eapply IHc2.
  auto.
  rewrite H2 in H.
  inversion H.
  rewrite H1 in H; inversion H.
Qed.

Open Local Scope tmp_scope.

Inductive tritra : assrt -> wpAssrt -> Prop :=

  | tritra_incons : forall pi sig Q, 
    (forall s h, (assrt_interp (pi, sig) s h) -> False) -> 
    tritra (pi, sig) Q

  | tritra_entail : forall P Q, 
    assrt_interp P ==> Assrt_interp Q -> 
    tritra P (wpElt Q)

  | tritra_precond_stre : forall L1 L1' L2,
    assrt_interp L1 ==> assrt_interp L1' -> 
    tritra L1' L2 ->
    tritra L1 L2

  | tritra_if : forall pi1 sig1 L1 L2 b,
    tritra (pi1 &&& b, sig1)  L1 ->
    tritra (pi1 &&& (neg_b b), sig1) L2 ->
    tritra (pi1, sig1) (wpIf b L1 L2)

  | tritra_mutation : forall pi1 sig1 e1 e2 e3 e4 L, 
    (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e3) s = true) ->
    tritra (pi1, sig1 ** (singl e1 e4)) L ->
    tritra (pi1, sig1 ** (singl e1 e2)) (wpMutation e3 e4 L)
    
  | tritra_mutation' : forall pi1 sig1 e1 e3 e4 L, 
    (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e3) s = true) ->
    tritra (pi1, sig1 ** (singl e1 e4)) L ->
    tritra (pi1, sig1 ** (cell e1)) (wpMutation e3 e4 L)

  | tritra_lookup : forall pi1 sig1 e1 e2 e x L, 
    (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e) s = true) ->
    tritra (pi1, sig1 ** (singl e1 e2)) (wpSubst ((x,e2)::nil) L) ->
    tritra (pi1, sig1 ** (singl e1 e2)) (wpLookup x e L)

  | tritra_lookup' : forall pi1 sig1 e1 e x L x', 
    (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e) s = true) ->
    fresh_assrt x' (pi1, sig1 ** cell e1) ->
    fresh_wpAssrt x' (wpLookup x e L) ->
    tritra (pi1, sig1 ** (singl e1 (var_e x'))) (wpSubst ((x,var_e x')::nil) L) ->
    tritra (pi1, sig1 ** (cell e1)) (wpLookup x e L)

  | tritra_subst_elt : forall pi1 sig1 l L, 
    tritra (pi1, sig1) (wpElt (subst_Assrt_lst l L)) ->
    tritra (pi1, sig1) (wpSubst l (wpElt L))
    
  | tritra_subst_subst : forall pi1 sig1 l1 l2 L, 
    tritra (pi1, sig1) (wpSubst (l2 ++ l1) L) ->
    tritra (pi1, sig1) (wpSubst l1 (wpSubst l2 L))
    
  | tritra_subst_lookup : forall pi1 sig1 e1 e2 e x x' l L,
    (forall s, eval_pi pi1 s = true -> eval_pi (e1 == (subst_e_lst l e)) s = true) ->                     
    fresh_lst x' l ->
    fresh_wpAssrt x' L ->
    fresh_e x' (var_e x) ->
    tritra (pi1, sig1 ** (singl e1 e2)) (wpSubst ((x, var_e x')::l ++ ((x', e2)::nil)) L) ->
    tritra (pi1, sig1 ** (singl e1 e2)) (wpSubst l (wpLookup x e L))

  | tritra_subst_lookup2 : forall pi1 sig1 e1 e x x' l L x'',
    (forall s, eval_pi pi1 s = true -> eval_pi (e1 == subst_e_lst l e) s = true) ->                     
    fresh_lst x' l ->
    fresh_wpAssrt x' L ->
    fresh_e x' (var_e x) ->
    fresh_wpAssrt x'' (wpSubst l (wpLookup x e L)) ->
    fresh_assrt x'' (pi1, sig1 ** cell e1) ->
    tritra (pi1, sig1 ** (singl e1 (var_e x''))) (wpSubst ((x, var_e x')::l ++ ((x',var_e x'')::nil)) L) ->
    tritra (pi1, sig1 ** cell e1) (wpSubst l (wpLookup x e L))
  
  | tritra_subst_mutation : forall pi1 sig1 e1 e2 l L, 
    tritra (pi1, sig1) (wpMutation (subst_e_lst l e1) (subst_e_lst l e2) (wpSubst l L)) ->
    tritra (pi1, sig1) (wpSubst l (wpMutation e1 e2 L))

  | tritra_subst_if : forall pi1 sig1 l b L1 L2,
    tritra (pi1, sig1)  (wpIf (subst_b_lst l b) (wpSubst l L1) (wpSubst l L2)) ->
    tritra (pi1, sig1) (wpSubst l (wpIf b L1 L2))

  (* regle generale pour prouver de maniere plus simple les 4 du dessous *)

 (* regle generale pour prouver de maniere plus simple les 4 du dessous *)

  | tritra_destruct_lst: forall pi1 sig1 e1 e2 L x', 
    (forall s, eval_pi pi1 s = true -> eval_pi (e1 =/= e2) s = true) ->
    fresh_assrt x' (pi1, sig1 ** lst e1 e2) ->
    fresh_wpAssrt x' L ->
    tritra (pi1 &&& (e1 =/= var_e x') &&& (var_e x' == nat_e 0), 
      sig1 ** (((singl e1 (var_e x')) ** (cell (e1 +e nat_e 1))) ** (lst (var_e x') e2))) L ->
    tritra (pi1 &&& (e1 =/= var_e x') &&& (var_e x' =/= nat_e 0), 
      sig1 ** (((singl e1 (var_e x')) ** (cell (e1 +e nat_e 1))) ** (lst (var_e x') e2))) L ->
    tritra (pi1,star sig1 (lst e1 e2)) L

  (**)

.

Close Local Scope tmp_scope.

Lemma tritra_soundness : forall P Q, tritra P Q -> 
  assrt_interp P ==> wpAssrt_interp Q.
  intros.
  induction H.

  red; intros.
  generalize (H _ _ H0); contradiction.

  red; simpl; intros.
  red in H; simpl in H.
  apply H; auto.

  red; intros.
  apply IHtritra.
  apply H.
  auto.

  red; simpl; intros.
  red in IHtritra1; simpl in IHtritra1.
  red in IHtritra2; simpl in IHtritra2.
  split.
  intuition.
  intros.
  eapply IHtritra2.
  split.
  apply andb_true_intro.
  split.
  apply (proj1 H1).
  apply (negb_false_is_true).
  rewrite <- negb_intro.
  auto.
  apply (proj2 H1).

  red; simpl; intros.
  inversion_clear H1.
  Decompose_sepcon H3 h1 h2.
  red in IHtritra.
  simpl in IHtritra.
  exists e2.
  generalize (H _ H2); intros.
  Compose_sepcon h2 h1.
  unfold eval_pi in H2; unfold eval_pi in H6.
  Mapsto.
  Intro_sepimp h2'  h'.
  eapply IHtritra.
  split; auto.
  Compose_sepcon h1 h2'.
  auto.
  unfold eval_pi in H2; unfold eval_pi in H6.
  split.
  Mapsto.
  auto.

  red; simpl; intros.
  red in IHtritra; simpl in IHtritra.
  inversion_clear H1.
  Decompose_sepcon H3 h1 h2.
  generalize (H _ H2); intros.
  inversion_clear H6.
  inversion_clear H5.
  exists (int_e x).
  Compose_sepcon h2 h1.
  Mapsto.
  generalize (H s H2); intros.
  unfold eval_pi in H2; unfold eval_pi in H5.
  Omega_exprb.
  Intro_sepimp h2' h'.
  eapply IHtritra.
  split; auto.
  Compose_sepcon h1 h2'.
  auto.
  split.  
  Mapsto.
  generalize (H s H2); intro.
  unfold eval_pi in H10.
  Omega_exprb.
  auto.  

  red; simpl; intros.
  red in IHtritra; simpl in IHtritra.
  inversion_clear H1.
  generalize (H _ H2); intros.
  Decompose_sepcon H3 h1 h2.
  exists e2.
  Compose_sepcon h2 h1.
  unfold eval_pi in H2; unfold eval_pi in H1.
  Mapsto.
  Intro_sepimp h2' h'.
  eapply IHtritra.
  split; auto.
  Compose_sepcon h1 h2'.
  auto.
  split.
  unfold eval_pi in H2; unfold eval_pi in H1.
  Mapsto.
  auto.

  red; simpl; intros.
  red in IHtritra.
  inversion_clear H3.
  Decompose_sepcon H5 h1 h2.
  inversion_clear H7.
  assert (assrt_interp (pi1, star sig1 (singl e1 (var_e x'))) (store.update x' x0 s) h).
  simpl.
  split.
  assert (fresh_b x' pi1).
  Max_inf_resolve.
  assert (In x' (x'::nil)).
  simpl; left; auto.
  generalize (fresh_b_inde pi1 x' true H7 s h x' x0 H10); intros.
  intuition.
  Compose_sepcon h1 h2.
  assert (fresh_Sigma x' sig1).
  Max_inf_resolve.
  assert (In x' (x'::nil)).
  simpl; left; auto.
  generalize (var_max_Sigma_inde sig1 x' H7 s h1 x' x0 H10); intros.
  intuition.
  assert (fresh_e x' e1).
  Max_inf_resolve.
  assert (In x' (x'::nil)).
  simpl; left; auto.
  split.
  Mapsto.
  rewrite fresh_e_eval; auto.
  rewrite fresh_e_eval; auto.
  generalize (IHtritra _ _ H7); intros.
  simpl in H10.
  exists (int_e (eval (var_e x') (store.update x' x0 s))).
  simpl.
  rewrite store.lookup_update'.
  Compose_sepcon h2 h1.
  generalize (H s H4); intros.
  unfold eval_pi in H11.
  Mapsto.
  Intro_sepimp h' h''.
  red in H10.
  red.
  simpl in H10.
  simpl. 
  rewrite store.lookup_update' in H10.
  rewrite store.update_update in H10.
  assert (fresh_wpAssrt x' L).
  Max_inf_resolve.
  assert (In x' (x'::nil)).
  simpl; left; auto.
  eapply (proj2 (fresh_wpAssrt_inde L x' H14 (store.update x x0 s) h'' x' x0 H15)); intros.
  assert (h' = h2).
  eapply singleton_equal.
  apply H12.
  apply H8.
  generalize (H s H4); intros.
  unfold eval_pi in H16.
  Omega_exprb.
  auto.
  subst h'.
  cutrewrite (h'' = h).
  auto.
  Equal_heap.
  Max_inf_resolve.
  
  (* case tritra_subst_elt *)

  red; simpl; intros.
  red in IHtritra; simpl in IHtritra.
  generalize (IHtritra _ _ H0); intros.
  eapply subst_lst2update_store_Assrt_interp.
  auto.

  (* case tritra_subst_subst *)

  red; simpl; intros.
  red in IHtritra; simpl in IHtritra.
  generalize (IHtritra _ _ H0); intros.
  apply subst_lst2update_store_app.
  auto.

  (* case tritra_subst_lookup *)

  red; simpl; intros.
  red in IHtritra; simpl in IHtritra.
  generalize (IHtritra _ _ H4); intros.
  generalize (H _  (proj1 H4)); intros.
  inversion_clear H4.
  Decompose_sepcon H8 h1 h2.
  apply (subst_lst2update_store_exists l 
    (fun e0 s h => (e |-> e0 ** (e |-> e0 -* update_store2 x e0 (wpAssrt_interp L))) s h) 
    s h).

  exists (int_e (eval e2 s)).

  assert (
    (fun s0 h0 => 
      (e |-> int_e (eval e2 s) ** (e |-> int_e (eval e2 s) -* update_store2 x (int_e (eval e2 s)) (wpAssrt_interp L))) s0 h0)
    = 
    (e |-> int_e (eval e2 s) ** (e |-> int_e (eval e2 s) -* update_store2 x (int_e (eval e2 s)) (wpAssrt_interp L)))
  ).
  apply sep.assert_ext.
  red.
  intuition.
  rewrite H11; clear H11.

  apply subst_lst2update_store_sep_con.
  Compose_sepcon h2 h1.
  apply subst_lst2update_store_mapsto.  
  unfold eval_pi in H6.
  Mapsto.
  rewrite subst_e_lst_int_e; auto.

  apply subst_lst2update_store_sepimp.
  Intro_sepimp h2' h'.
  unfold update_store2.
  simpl.

  assert (h2 = h2').
  eapply singleton_equal.
  apply H10.
  generalize (subst_lst2update_store_mapsto' _ _ _ _ _ H13); intros.
  apply H15.
  unfold eval_pi in H6.
  Omega_exprb.
  rewrite subst_e_lst_int_e; auto.
  subst h2'.

  assert (h = h').
  Equal_heap.
  subst h'.

  rewrite <- H15.
  generalize (subst_lst2update_store' _ _ _ _ _ _ H5); intro.
  unfold update_store2 in H13.
  apply intro_fresh_var with x'; auto.

  (* case tritra_subst_lookup' *)
  
  red; intros.
  red in IHtritra.
  inversion_clear H6.
  simpl in H8.
  Decompose_sepcon H8 h1 h2.
  inversion_clear H10.
  assert (assrt_interp (pi1, star sig1 (singl e1 (var_e x''))) (store.update x'' x0 s) h).
  
  simpl.
  split.
  assert (fresh_b x'' pi1).
  Max_inf_resolve.
  assert (In x'' (x''::nil)).
  simpl; left; auto.
  generalize (fresh_b_inde pi1 x'' true H10 s h x'' x0 H13); intros.
  intuition.
  Compose_sepcon h1 h2.
  assert (fresh_Sigma x'' sig1).
  Max_inf_resolve.
  assert (In x'' (x''::nil)).
  simpl; left; auto.
  generalize (var_max_Sigma_inde sig1 x'' H10 s h1 x'' x0 H13); intros.
  intuition.
  assert (fresh_e x'' e1).
  Max_inf_resolve.
  assert (In x'' (x''::nil)).
  simpl; left; auto.
  split.  
  Mapsto.
  rewrite fresh_e_eval; auto.
  rewrite fresh_e_eval; auto.
  generalize (IHtritra _ _ H10); intros.
  clear H10.
  cut (wpAssrt_interp (wpSubst l (wpLookup x e L)) (store.update x'' x0 s) h).
  intros.
  assert (In x'' (x''::nil)).
  simpl; left; auto.
  generalize (fresh_wpAssrt_inde (wpSubst l (wpLookup x e L)) x'' H3 s h x'' x0 H14); intros.
  intuition.
  simpl.
  apply (subst_lst2update_store_exists l 
    (fun e0 s h => (e |-> e0 ** (e |-> e0 -* update_store2 x e0 (wpAssrt_interp L))) s h) 
    (store.update x'' x0 s) h).

  exists (int_e x0).

  assert (
    (fun s0 h0 => 
      (e |-> int_e x0 ** (e |-> int_e x0 -* update_store2 x (int_e x0) (wpAssrt_interp L))) s0 h0)
    = 
      (e |-> int_e x0 ** (e |-> int_e x0 -* update_store2 x (int_e x0) (wpAssrt_interp L)))
  ).
  apply sep.assert_ext.
  red.
  intuition.
  rewrite H10; clear H10.

  apply subst_lst2update_store_sep_con.
  Compose_sepcon h2 h1.
  assert (inde (x''::nil) (e |-> int_e x0)).
  red; intros.
  simpl in H10; inversion_clear H10; try contradiction.
  subst x1.
  split; intros; Mapsto.
  rewrite fresh_e_eval; auto.
  Max_inf_resolve.
  rewrite fresh_e_eval; auto.
  Max_inf_resolve.
  assert (fresh_lst x'' l).
  Max_inf_resolve.
  assert (In x'' (x''::nil)).
  intuition.
  eapply (proj1 (fresh_lst_inde l (e |-> int_e x0) x'' H10 H14 s h2 x'' x0 H15)).  

  apply subst_lst2update_store_mapsto.
  generalize (H s H7); intros.
  unfold eval_pi in H16.
  Mapsto.
  rewrite subst_e_lst_int_e; auto.

  apply subst_lst2update_store_sepimp.
  Intro_sepimp h2' h'.
  unfold update_store2.
  simpl.

  assert (h2 = h2').
  assert ((e1 |-> int_e x0) (store.update x'' x0 s) h2).
  Mapsto.
  rewrite fresh_e_eval; auto.
  Max_inf_resolve.
    
  eapply singleton_equal.
  apply H16.
  generalize (subst_lst2update_store_mapsto' _ _ _ _ _ H14); intros.
  apply H17.
  rewrite fresh_e_eval.
  rewrite subst_e_lst_eval.
  generalize (H s H7); intros.
  unfold eval_pi in H17.
  Omega_exprb.
  Max_inf_resolve.
  Max_inf_resolve.
  Max_inf_resolve.
  rewrite subst_e_lst_int_e; auto.
  subst h2'.

  assert (h = h').
  Equal_heap.
  subst h'.

  rewrite <- H16.
  simpl in H13.
  generalize (subst_lst2update_store' _ _ _ _ _ _ H13); intro.
  unfold update_store2 in H15.
  simpl in H15.
  rewrite store.lookup_update' in H15.
  cut (
     subst_lst2update_store l
        (fun (s0 : store.s) (h0 : heap.h) =>
        wpAssrt_interp L (store.update x (eval (int_e x0) (store.update x'' x0 s)) s0) h0) (store.update x'' x0 s) h
   ).
  auto.
  eapply intro_fresh_var with x'; auto.

  (* case tritra_subst_mutation *)

  red; simpl; intros.
  red in IHtritra; simpl in IHtritra.
  generalize (IHtritra _ _ H0); intros.
  eapply subst_lst2update_store_lookup.
  auto.

  (* case tritra_subst_if *)

  red; simpl; intros.
  red in IHtritra; simpl in IHtritra.
  generalize (IHtritra _ _ H0); intros.
  inversion_clear H1.
  apply (subst_lst2update_store_and' l (fun s0 h0 => eval_pi b s0 = true -> wpAssrt_interp L1 s0 h0) (fun s0 => fun h0 =>  eval_pi b s0 = false -> wpAssrt_interp L2 s0 h0) s h).
  split.
  apply (subst_lst2update_store_imply l (fun s => fun h => eval_pi b s = true) (fun s => fun h => wpAssrt_interp L1 s h) s h).
  intros.
  generalize (H2 (subst_lst2update_store_subst_b_lst true _ _ _ _ H1)); intros.
  assert (wpAssrt_interp L1 = (fun s => fun h => wpAssrt_interp L1 s h)).
  eapply sep.assert_ext.
  red; simpl.
  tauto.
  rewrite <- H5.
  auto.
  apply (subst_lst2update_store_imply l (fun s => fun h => eval_b b s = false) (fun s => fun h => wpAssrt_interp L2 s h) s h).
  intros.
  generalize (H3 (subst_lst2update_store_subst_b_lst false _ _ _ _ H1)); intros.
  assert (wpAssrt_interp L2 = (fun s => fun h => wpAssrt_interp L2 s h)).
  eapply sep.assert_ext.
  red; simpl.
  tauto.
  rewrite <- H5.
  auto.

  (* case regle generale *)

  red; simpl; intros.
  clear H2 H3.
  inversion_clear H4.
  Decompose_sepcon H3 h1 h2.
  destruct H7.
  generalize (H s H2); intros.
  unfold eval_pi in H8.
  Omega_exprb. 
  assert (Choice: eval e2 s = 0%Z \/ eval e2 s <> 0%Z).
  omega.
  inversion_clear Choice as [X1 | X2].

(**)

  red in IHtritra1; simpl in IHtritra1.
  
  cut (
    (wpAssrt_interp L) (store.update x' (eval e2 s) s) h
  ).

  intros.

  assert (In x' (x'::nil)).
  simpl; left; auto.

  apply (proj2 (fresh_wpAssrt_inde L x' H1 s h x' (eval e2 s) H14)).
  auto.
  
  eapply (IHtritra1).
  split.

  assert (fresh_b x' pi1).
  Max_inf_resolve.

  assert (In x' (x'::nil)).
  simpl; left; auto.  
  
  eapply andb_true_intro.
  split.
  eapply andb_true_intro.
  split.

  apply (proj1 (fresh_b_inde pi1 x' true H13 s h x' (eval e2 s) H14)); auto.

  rewrite fresh_e_eval.
  rewrite store.lookup_update'.
  assert ((eval e1 s) <> (eval e2 s)).
  destruct H12.
  Omega_exprb.
  Decompose_sepcon H11 h21 h22.
  Decompose_sepcon H19 h41 h42.
  eapply singl_disjoint_neq.
  apply H21.
  apply H23.
  Disjoint_heap.
  rewrite (Zeq_bool_false'' _ _ H15); auto.
  Max_inf_resolve.
  
  rewrite store.lookup_update'.
  rewrite X1; eapply Zeq_bool_refl.
  Compose_sepcon h1 h0.

  assert (fresh_Sigma x' sig1).
  Max_inf_resolve.  

  assert (In x' (x'::nil)).
  simpl; left; auto.  

  apply (proj1 (var_max_Sigma_inde sig1 _ H13 s h1 x' (eval e2 s) H14)); auto.
  
  Compose_sepcon h2 h3.
  Decompose_sepcon H11 h21 h22.
  Compose_sepcon h21 h22.
  split.

  Mapsto.  

  rewrite fresh_e_eval; auto.
  Max_inf_resolve.    

  rewrite fresh_e_eval; auto.
  Max_inf_resolve.    

  split.

  exists (eval e4 s).

  Mapsto.
  rewrite fresh_e_eval; auto.
  Max_inf_resolve.    

  rewrite fresh_e_eval; auto.
  Max_inf_resolve.    

  eapply Lst_equiv'.
  apply H12.
  simpl.
  rewrite store.lookup_update'.
  auto.
  
  rewrite fresh_e_eval; auto.
  Max_inf_resolve.

(**)

  red in IHtritra2; simpl in IHtritra2.
  
  cut (
    (wpAssrt_interp L) (store.update x' (eval e2 s) s) h
  ).

  intros.

  assert (In x' (x'::nil)).
  simpl; left; auto.

  apply (proj2 (fresh_wpAssrt_inde L x' H1 s h x' (eval e2 s) H14)).
  auto.
  
  eapply (IHtritra2).
  split.

  assert (fresh_b x' pi1).
  Max_inf_resolve.

  assert (In x' (x'::nil)).
  simpl; left; auto.  
  
  eapply andb_true_intro.
  split.
  eapply andb_true_intro.
  split.

  apply (proj1 (fresh_b_inde pi1 x' true H13 s h x' (eval e2 s) H14)); auto.

  rewrite fresh_e_eval.
  rewrite store.lookup_update'.
  assert ((eval e1 s) <> (eval e2 s)).
  destruct H12.
  Omega_exprb.
  Decompose_sepcon H11 h21 h22.
  Decompose_sepcon H19 h41 h42.
  eapply singl_disjoint_neq.
  apply H21.
  apply H23.
  Disjoint_heap.
  rewrite (Zeq_bool_false'' _ _ H15); auto.
  Max_inf_resolve.
  
  rewrite store.lookup_update'.
  rewrite (proj2 (Zeq_bool_false (eval e2 s) 0%Z)).
  auto.
  auto.
  Compose_sepcon h1 h0.

  assert (fresh_Sigma x' sig1).
  Max_inf_resolve.  

  assert (In x' (x'::nil)).
  simpl; left; auto.  

  apply (proj1 (var_max_Sigma_inde sig1 _ H13 s h1 x' (eval e2 s) H14)); auto.
  
  Compose_sepcon h2 h3.
  Decompose_sepcon H11 h21 h22.
  Compose_sepcon h21 h22.
  split.

  Mapsto.  

  rewrite fresh_e_eval; auto.
  Max_inf_resolve.    

  rewrite fresh_e_eval; auto.
  Max_inf_resolve.    

  split.

  exists (eval e4 s).

  Mapsto.
  rewrite fresh_e_eval; auto.
  Max_inf_resolve.    

  rewrite fresh_e_eval; auto.
  Max_inf_resolve.    

  eapply Lst_equiv'.
  apply H12.
  simpl.
  rewrite store.lookup_update'.
  auto.
  
  rewrite fresh_e_eval; auto.
  Max_inf_resolve.
Qed.

Definition triple_vfresh (a: assrt) (L: wpAssrt) := (max (var_max_assrt a) (var_max_wpAssrt L)) + 1.

Lemma tritra_lookup_lst: forall pi1 sig1 e1 e2 e x L x', 
    (forall s, eval_pi pi1 s = true -> (eval_pi (e1 == e) s = true /\ eval_pi (e1 =/= e2) s = true)) ->

    x' = triple_vfresh  (pi1, star sig1 (lst e1 e2)) (wpLookup x e L) ->

    tritra (pi1 &&& (e1 =/= var_e x') &&& (var_e x' == nat_e 0), 
      star (star sig1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))) (wpLookup x e L) ->
    tritra (pi1 &&& (e1 =/= var_e x') &&& (var_e x' =/= nat_e 0), 
      star (star sig1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))) (wpLookup x e L) ->

    tritra (pi1, star sig1 (lst e1 e2)) (wpLookup x e L).

  intros.

  unfold triple_vfresh in H0.

  eapply tritra_destruct_lst with (x' := x').
  intros.
  generalize (H s H3); intro X; inversion_clear X.
  auto.
  
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  
  eapply tritra_precond_stre; [idtac | eapply H1].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h212 +++ h22 +++ h1) (h211); auto.
  Compose_sepcon h1 (h212 +++ h22); auto.
  Compose_sepcon h22 h212; auto.

  eapply tritra_precond_stre; [idtac | eapply H2].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h212 +++ h22 +++ h1) (h211); auto.
  Compose_sepcon h1 (h212 +++ h22); auto.
  Compose_sepcon h22 h212; auto.
Qed.

Lemma tritra_lookup_lst': forall pi1 sig1 e1 e2 e x L x', 
    (forall s, eval_pi pi1 s = true -> (eval_pi ((e1 +e nat_e 1) == e) s = true /\ eval_pi (e1 =/= e2) s = true)) ->

    x' = triple_vfresh  (pi1, star sig1 (lst e1 e2)) (wpLookup x e L) ->

    tritra (pi1 &&& (e1 =/= var_e x') &&& (var_e x' == nat_e 0), 
      star (star sig1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))) (wpLookup x e L) ->
    tritra (pi1 &&& (e1 =/= var_e x') &&& (var_e x' =/= nat_e 0), 
      star (star sig1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))) (wpLookup x e L) ->

    tritra (pi1, star sig1 (lst e1 e2)) (wpLookup x e L).

  intros.

  unfold triple_vfresh in H0.

  eapply tritra_destruct_lst with (x' := x').
  intros.
  generalize (H s H3); intro X; inversion_clear X.
  auto.
  
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  
  eapply tritra_precond_stre; [idtac | eapply H1].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h212 +++ h22 +++ h1) (h211); auto.
  Compose_sepcon h1 (h212 +++ h22); auto.
  Compose_sepcon h22 h212; auto.

  eapply tritra_precond_stre; [idtac | eapply H2].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h212 +++ h22 +++ h1) (h211); auto.
  Compose_sepcon h1 (h212 +++ h22); auto.
  Compose_sepcon h22 h212; auto.
Qed.

Lemma tritra_subst_lookup_lst: forall pi1 sig1 e1 e2 e x L l x', 
    (forall s, eval_pi pi1 s = true -> (eval_pi (e1 == (subst_e_lst l e)) s = true /\ eval_pi (e1 =/= e2) s = true)) ->
    x' = triple_vfresh  (pi1, star sig1 (lst e1 e2)) (wpSubst l (wpLookup x e L)) ->
    tritra (pi1 &&& (e1 =/= var_e x') &&& (var_e x' == nat_e 0),
      star (star sig1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))) (wpSubst l (wpLookup x e L)) ->
    tritra (pi1 &&& (e1 =/= var_e x') &&& (var_e x' =/= nat_e 0),
      star (star sig1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))) (wpSubst l (wpLookup x e L)) ->
    tritra (pi1, star sig1 (lst e1 e2)) (wpSubst l (wpLookup x e L)).
  intros.

  unfold triple_vfresh in H0.

  eapply tritra_destruct_lst with (x' := x').
  intros.
  generalize (H s H3); intro X; inversion_clear X.
  auto.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  auto.

  eapply tritra_precond_stre; [idtac | eapply H1].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h212 +++ h22 +++ h1) (h211); auto.
  Compose_sepcon h1 (h212 +++ h22); auto.
  Compose_sepcon h22 h212; auto.

  eapply tritra_precond_stre; [idtac | eapply H2].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h212 +++ h22 +++ h1) (h211); auto.
  Compose_sepcon h1 (h212 +++ h22); auto.
  Compose_sepcon h22 h212; auto.
Qed.

Lemma tritra_subst_lookup_lst': forall pi1 sig1 e1 e2 e x L l x', 
    (forall s, eval_pi pi1 s = true -> (eval_pi ((e1 +e nat_e 1) == (subst_e_lst l e)) s = true /\ eval_pi (e1 =/= e2) s = true)) ->
    x' = triple_vfresh  (pi1,star sig1 (lst e1 e2)) (wpSubst l (wpLookup x e L)) ->
    tritra (pi1 &&& (e1 =/= var_e x')  &&& (var_e x' == nat_e 0),
      star (star sig1 (star (lst (var_e x') e2) (singl e1 (var_e x')))) (cell (e1 +e nat_e 1))) (wpSubst l (wpLookup x e L)) ->
    tritra (pi1 &&& (e1 =/= var_e x')  &&& (var_e x' =/= nat_e 0),
      star (star sig1 (star (lst (var_e x') e2) (singl e1 (var_e x')))) (cell (e1 +e nat_e 1))) (wpSubst l (wpLookup x e L)) ->
    tritra (pi1,star sig1 (lst e1 e2)) (wpSubst l (wpLookup x e L)).
  intros.
  unfold triple_vfresh in H0.
  eapply tritra_destruct_lst with (x' := x').
  intros.
  generalize (H s H3); intro X; inversion_clear X.
  auto.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  auto.

  eapply tritra_precond_stre; [idtac | eapply H1].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h211 +++ h22 +++ h1) (h212); auto.
  Compose_sepcon h1 (h211 +++ h22); auto.
  Compose_sepcon h22 h211; auto.

  eapply tritra_precond_stre; [idtac | eapply H2].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h211 +++ h22 +++ h1) (h212); auto.
  Compose_sepcon h1 (h211 +++ h22); auto.
  Compose_sepcon h22 h211; auto.
Qed.

Lemma tritra_mutation_lst : forall pi1 sig1 e1 e2 e3 e4 L x', 
    (forall s, eval_pi pi1 s = true -> (eval_pi (e1 == e3) s = true /\ eval_pi (e1 =/= e2) s = true)) ->
    x' = triple_vfresh (pi1,star sig1 (lst e1 e2)) (wpMutation e3 e4 L) ->
    tritra (pi1 &&& (e1 =/= var_e x') &&& (var_e x' == nat_e 0), 
      star (star sig1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))) (wpMutation e3 e4 L) ->
    tritra (pi1 &&& (e1 =/= var_e x') &&& (var_e x' =/= nat_e 0), 
      star (star sig1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))) (wpMutation e3 e4 L) ->
    tritra (pi1,star sig1 (lst e1 e2)) (wpMutation e3 e4 L).
  intros.
  unfold triple_vfresh in H0.
  eapply tritra_destruct_lst with (x' := x').
  intros.
  generalize (H s H3); intro X; inversion_clear X.
  auto.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  auto.

  eapply tritra_precond_stre; [idtac | eapply H1].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h212 +++ h22 +++ h1) (h211); auto.
  Compose_sepcon h1 (h212 +++ h22); auto.
  Compose_sepcon h22 h212; auto.

  eapply tritra_precond_stre; [idtac | eapply H2].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h212 +++ h22 +++ h1) (h211); auto.
  Compose_sepcon h1 (h212 +++ h22); auto.
  Compose_sepcon h22 h212; auto.
Qed.

Lemma tritra_mutation_lst': forall pi1 sig1 e1 e2 e3 e4 L x', 
    (forall s, eval_pi pi1 s = true -> (eval_pi ((e1 +e (nat_e 1)) == e3) s = true /\ eval_pi (e1 =/= e2) s = true)) ->
    x' = triple_vfresh (pi1, star sig1 (lst e1 e2)) (wpMutation e3 e4 L) ->
    tritra (pi1 &&& (e1 =/= var_e x')  &&& (var_e x' == nat_e 0), 
      star (star sig1 (star (lst (var_e x') e2) (singl e1 (var_e x')))) (cell (e1 +e nat_e 1))) (wpMutation e3 e4 L) ->
    tritra (pi1 &&& (e1 =/= var_e x')  &&& (var_e x' =/= nat_e 0), 
      star (star sig1 (star (lst (var_e x') e2) (singl e1 (var_e x')))) (cell (e1 +e nat_e 1))) (wpMutation e3 e4 L) ->
    tritra (pi1, star sig1 (lst e1 e2)) (wpMutation e3 e4 L).
  intros.
  unfold triple_vfresh in H0.
  eapply tritra_destruct_lst with (x' := x').
  intros.
  generalize (H s H3); intro X; inversion_clear X.
  auto.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  auto.


  eapply tritra_precond_stre; [idtac | eapply H1].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h211 +++ h22 +++ h1) (h212); auto.
  Compose_sepcon h1 (h211 +++ h22); auto.
  Compose_sepcon h22 h211; auto.

  eapply tritra_precond_stre; [idtac | eapply H2].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h211 +++ h22 +++ h1) (h212); auto.
  Compose_sepcon h1 (h211 +++ h22); auto.
  Compose_sepcon h22 h211; auto.
Qed.

Lemma tritra_subst_mutation_lst: forall pi1 sig1 e1 e2 e3 e4 L l x', 
    (forall s, eval_pi pi1 s = true -> (eval_pi (e1 == (subst_e_lst l e3)) s = true /\ eval_pi (e1 =/= e2) s = true)) ->
    x' = triple_vfresh (pi1,star sig1 (lst e1 e2)) (wpSubst l (wpMutation e3 e4 L))->
    tritra (pi1 &&& (e1 =/= var_e x') &&& (var_e x' == nat_e 0), 
      star (star sig1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))) (wpSubst l (wpMutation e3 e4 L)) ->
    tritra (pi1 &&& (e1 =/= var_e x') &&& (var_e x' =/= nat_e 0), 
      star (star sig1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))) (wpSubst l (wpMutation e3 e4 L)) ->
    tritra (pi1,star sig1 (lst e1 e2)) (wpSubst l (wpMutation e3 e4 L)).

  intros.
  unfold triple_vfresh in H0.
  eapply tritra_destruct_lst with (x' := x').
  intros.
  generalize (H s H3); intro X; inversion_clear X.
  auto.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  auto.

  eapply tritra_precond_stre; [idtac | eapply H1].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h212 +++ h22 +++ h1) (h211); auto.
  Compose_sepcon h1 (h212 +++ h22); auto.
  Compose_sepcon h22 h212; auto.

  eapply tritra_precond_stre; [idtac | eapply H2].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h212 +++ h22 +++ h1) (h211); auto.
  Compose_sepcon h1 (h212 +++ h22); auto.
  Compose_sepcon h22 h212; auto.
Qed.

Lemma tritra_subst_mutation_lst': forall pi1 sig1 e1 e2 e3 e4 L l x', 
    (forall s, eval_pi pi1 s = true -> (eval_pi ((e1 +e nat_e 1) == (subst_e_lst l e3)) s = true /\ eval_pi (e1 =/= e2) s = true)) ->
    x' = triple_vfresh (pi1,star sig1 (lst e1 e2)) (wpSubst l (wpMutation e3 e4 L)) ->
    tritra (pi1 &&& (e1 =/= var_e x')  &&& (var_e x' == nat_e 0),
      star (star sig1 (star (lst (var_e x') e2) (singl e1 (var_e x')))) (cell (e1 +e nat_e 1))) (wpSubst l (wpMutation e3 e4 L)) ->
    tritra (pi1 &&& (e1 =/= var_e x')  &&& (var_e x' =/= nat_e 0),
      star (star sig1 (star (lst (var_e x') e2) (singl e1 (var_e x')))) (cell (e1 +e nat_e 1))) (wpSubst l (wpMutation e3 e4 L)) ->
    tritra (pi1,star sig1 (lst e1 e2)) (wpSubst l (wpMutation e3 e4 L)).

  intros.
  unfold triple_vfresh in H0.
  eapply tritra_destruct_lst with (x' := x').
  intros.
  generalize (H s H3); intro X; inversion_clear X.
  auto.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  
  red; intros.
  subst x'.
  simpl.  
  repeat Resolve_ge_max.
  auto.

  eapply tritra_precond_stre; [idtac | eapply H1].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h211 +++ h22 +++ h1) (h212); auto.
  Compose_sepcon h1 (h211 +++ h22); auto.
  Compose_sepcon h22 h211; auto.

  eapply tritra_precond_stre; [idtac | eapply H2].
  red; intros.
  inversion_clear H3.
  split; auto.
  simpl in H5.
  Decompose_sepcon H5 h1 h2.
  Decompose_sepcon H8 h21 h22.
  Decompose_sepcon H8 h211 h212.
  simpl.
  Compose_sepcon (h211 +++ h22 +++ h1) (h212); auto.
  Compose_sepcon h1 (h211 +++ h22); auto.
  Compose_sepcon h22 h211; auto.
Qed.

(********************************)
(* Tactics to resolve tritra goals *)
(********************************)

(*
 * Resolution tactic 
 *)

Lemma tritra_use: forall c P Q R, 
  wp_frag (Some (wpElt Q)) c = Some R -> 
  tritra P R -> 
  {{ assrt_interp P }} c {{ Assrt_interp Q }}.
  intros.
  generalize (wp_frag_soudness _ _ _ H); intros.
  simpl in H1.
  eapply semax_strengthen_pre with (wpAssrt_interp R); [apply tritra_soundness; auto | auto].
Qed.

(* the following lemma replaces the constructor tritra_subst_lookup in the tactic,
  the difference is that it introduces a way to compute fresh variables *)
Lemma tritra_subst_lookup' : forall pi1 sig1 e1 e2 e x x' l L,
  (forall s,eval_pi pi1 s = true -> (eval_pi (e1 == (subst_e_lst l e))) s = true) ->                     
  x' = triple_vfresh (pi1,star sig1 (singl e1 e2)) (wpSubst l (wpLookup x e L)) ->
  tritra (pi1,star sig1 (singl e1 e2)) (wpSubst ((x,(var_e x'))::l ++ ((x',e2)::nil)) L) ->
  tritra (pi1,star sig1 (singl e1 e2)) (wpSubst l (wpLookup x e L)).
  intros.
  unfold triple_vfresh in H0.
  apply tritra_subst_lookup with x'.
  auto.
  red.
  rewrite H0.
  simpl.
  Resolve_ge_max.
  Resolve_ge_max.
  red.
  rewrite H0.
  simpl.
  Resolve_ge_max.
  Resolve_ge_max.
  red.
  rewrite H0.
  simpl.
  simpl.
  Resolve_ge_max.
  Resolve_ge_max.
  auto.
Qed.

Ltac Rotate_tritra_sig_lhs :=
  match goal with
    | |- tritra (?pi,?sig) ?L' =>
      eapply tritra_precond_stre with (
        (pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp))
      ); [apply entail_soundness; simpl; Entail| simpl]
  end.

Lemma Decompose_Assrt_interp: forall a hd tl,
  (assrt_interp a ==> assrt_interp hd) \/ (assrt_interp a ==> Assrt_interp tl) ->
  (assrt_interp a ==> (Assrt_interp (hd::tl))).
  red; intros; simpl; intuition.
Qed.

Ltac Resolve_entails :=
  eapply Decompose_Assrt_interp; ((left; apply entail_soundness; Entail) || (right; Resolve_entails)).

Ltac tritra_resolve := 
  match goal with 
    
    | |- tritra (?pi1, ?sig1) ?L => eapply tritra_entail; Resolve_entails
      
    | |- tritra (?pi1, star ?sig1 (singl ?e1 ?e2)) (wpMutation ?e3 ?e4 ?L') => 
      (eapply tritra_mutation; [unfold eval_pi; Omega_exprb | tritra_resolve] || Rotate_tritra_sig_lhs; idtac)
      
    | |- tritra (?pi1, star ?sig1 (cell ?e1)) (wpMutation ?e3 ?e4 ?L') => 
      (eapply tritra_mutation'; [unfold eval_pi; Omega_exprb | tritra_resolve] || Rotate_tritra_sig_lhs; idtac)
      
    | |- tritra (?pi1, star ?sig1 (singl ?e1 ?e2)) (wpLookup ?x ?e ?L') => 
      (eapply tritra_lookup; [unfold eval_pi; Omega_exprb | tritra_resolve] || Rotate_tritra_sig_lhs; idtac)
      
    | |- tritra ?L (wpSubst ?l (wpElt ?L')) => eapply tritra_subst_elt; simpl; idtac
    | |- tritra ?L (wpSubst ?l (wpSubst ?l' ?L')) => eapply tritra_subst_subst; simpl; idtac
      
    | |- tritra ?L (wpSubst ?l (wpLookup ?x ?e ?L')) => 
      (eapply tritra_subst_lookup'; [unfold eval_pi; Omega_exprb | simpl; intuition | tritra_resolve] || Rotate_tritra_sig_lhs; idtac)
      
    | |- tritra ?L (wpSubst ?l (wpMutation ?e1 ?e2 ?L')) => eapply tritra_subst_mutation; simpl; idtac
    | |- tritra ?L (wpSubst ?l (wpIf ?b ?L1 ?L2)) => eapply tritra_subst_if; simpl; idtac
    | |- tritra ?L (wpIf ?b ?L1 ?L2) => eapply tritra_if; simpl; idtac
      
   end.

Ltac Tritra := Rotate_tritra_sig_lhs; repeat tritra_resolve.

(* TODO: heart *)
(* pi,sig is the pre-condition
   A is the current post-condition
   the result is a list of pre/post-conditions left to be proved
*)
Definition tritra_step' (pi : Pi) (sig : Sigma) (A : wpAssrt) : option (list ((Pi * Sigma) * wpAssrt)) :=
  match A with

    | wpElt L => 
      if entail_fct (pi, sig) L nil then
        Some nil else None

    | wpSubst l L =>
      match L with
        | wpElt L' => Some (((pi,sig), wpElt (subst_Assrt_lst l L'))::nil) 
        | wpSubst l' L' => Some (((pi,sig), wpSubst (l'++ l) L')::nil)
        | wpLookup x e L' => 
          match sig with
            | star s1 (singl e1 e2) => 
              if expr_b_dp (pi =b> (e1 == subst_e_lst l e)) then 
                let x' := (max (max (var_max_lst l) (var_max_wpAssrt L')) x) + 1 in 
                  Some (((pi,sig), wpSubst ((x, var_e x')::l ++ ((x',e2)::nil)) L')::nil)
                else 
                  Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp)), A)::nil)
            | star s1 (cell e1) => 
              if expr_b_dp (pi =b> (e1 == subst_e_lst l e)) then 
                let x' := (max (max (var_max_lst l) (var_max_wpAssrt L')) x) + 1 in 
                  let x'' := (max (var_max_assrt (pi,sig)) (var_max_wpAssrt A)) + 1 in
                    Some (((pi, star s1 (singl e1 (var_e x''))), wpSubst ((x, var_e x')::l ++ ((x', var_e x'')::nil)) L')::nil)
                else 
                  Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp)),A)::nil)
            | star s1 (lst e1 e2) => 
              if expr_b_dp (pi =b> ((e1 =/= e2) &&& (e1 == subst_e_lst l e))) then 
                let x' := triple_vfresh (pi,sig) A in 
                  Some ((pi &&& (e1 =/= var_e x') &&& (var_e x' == nat_e 0), 
                    star (star s1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x')), A)::
                      (pi &&& (e1 =/= var_e x') &&& (var_e x' =/= nat_e 0), 
                        star (star s1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x')), A)::
                      nil)
                else 
              if expr_b_dp (pi =b> ((e1 =/= e2) &&& ((e1 +e nat_e 1) == subst_e_lst l e))) then
                let x' := triple_vfresh (pi,sig) A in 
                  Some (
                       (((pi &&& (e1 =/= var_e x')) &&& (var_e x' == nat_e 0),
                       star (star s1 (star (lst (var_e x') e2) (singl e1 (var_e x'))))
                       (cell (e1 +e nat_e 1))), A)::
                       (((pi &&& (e1 =/= var_e x')) &&& (var_e x' =/= nat_e 0),
                       star (star s1 (star (lst (var_e x') e2) (singl e1 (var_e x'))))
                       (cell (e1 +e nat_e 1))), A)::
                      nil)
                else 
                  Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp)), A)::nil)
            | (singl e1 e2) => Some ((pi, star emp sig, A)::nil)
            | (cell e1) => Some ((pi, star emp sig, A)::nil)
            | (lst e1 e2) => Some ((pi, star emp sig, A)::nil)
            | _ => Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp)), A)::nil)
          end
        | wpMutation e1 e2 L' => 
          Some (((pi,sig), wpMutation (subst_e_lst l e1) (subst_e_lst l e2) (wpSubst l L'))::nil)
        | wpIf b L1 L2 => 
          Some (((pi,sig), wpIf (subst_b_lst l b) (wpSubst l L1) (wpSubst l L2))::nil)                  
      end
    (**)
    | wpIf b L1 L2 => 
      Some (((pi &&& b,sig),L1)::((pi &&& (! b),sig),L2)::nil)
    (**)
    | wpLookup x e L =>       
      match sig with
        | star s1 (singl e1 e2) => 
          if expr_b_dp (pi =b> (e1 == e)) then
            Some (((pi,sig), wpSubst ((x,e2)::nil) L)::nil)
            else 
              Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp)), A)::nil)

        | star s1 (cell e1) => 
          if expr_b_dp (pi =b> (e1 == e)) then
            let x' := (max (var_max_assrt (pi, sig)) (var_max_wpAssrt A)) + 1 in 
               Some (((pi, star s1 (singl e1 (var_e x'))), wpSubst ((x, var_e x')::nil) L)::nil)
            else 
              Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp)), A)::nil)
        | star s1 (lst e1 e2) => 
          if expr_b_dp (pi =b> ((e1 =/= e2) &&& (e1 == e))) then
            let x' := triple_vfresh (pi,sig) A in 
              Some (((pi &&& (e1 =/= var_e x') &&& (var_e x' == nat_e 0),
                star (star s1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))), A)::
              ((pi &&& (e1 =/= var_e x') &&& (var_e x' =/= nat_e 0),
                star (star s1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))), A)::
                  nil)
            else 
          if expr_b_dp (pi =b> ((e1 =/= e2) &&& ((e1 +e nat_e 1) == e))) then
            let x' := triple_vfresh (pi,sig) A in 
              Some (((pi &&& (e1 =/= var_e x') &&& (var_e x' == nat_e 0),
                star (star s1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))), A)::
                  ((pi &&& (e1 =/= var_e x') &&& (var_e x' =/= nat_e 0),
                    star (star s1 (star (lst (var_e x') e2) (cell (e1 +e nat_e 1)))) (singl e1 (var_e x'))), A)::
                  nil)
            else Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp)),A)::nil)  
        | (singl e1 e2) => Some ((pi, star emp sig, A)::nil)
        | (cell e1) => Some ((pi, star emp sig, A)::nil)
        | (lst e1 e2) => Some ((pi, star emp sig, A)::nil)
        | _ => Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp)), A)::nil)
      end
      (**)
    | wpMutation e1 e2 L => 
      match sig with
        | star s1 (cell e3) => 
          if expr_b_dp (pi =b> (e1 == e3)) then
            Some (((pi, star s1 (singl e3 e2)),L)::nil)
            else 
              Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp)), A)::nil)
        | star s1 (singl e3 e4) => 
          if expr_b_dp (pi =b> (e1 == e3)) then
            Some (((pi, star s1 (singl e3 e2)), L)::nil)
            else 
              Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp)), A)::nil)
        | star s1 (lst e3 e4) => 
              if expr_b_dp (pi =b> ((e1 == e3) &&& (e3 =/= e4))) then
                let x' := triple_vfresh (pi,sig) A in 
                  Some (
                  (((pi &&& (e3 =/= var_e x')) &&& (var_e x' == nat_e 0),
                  star (star s1 (star (lst (var_e x') e4) (cell (e3 +e nat_e 1))))
                  (singl e3 (var_e x'))), A)::
                  (((pi &&& (e3 =/= var_e x')) &&& (var_e x' =/= nat_e 0),
                  star (star s1 (star (lst (var_e x') e4) (cell (e3 +e nat_e 1))))
                  (singl e3 (var_e x'))),A)::
                  nil)
                else if expr_b_dp (pi =b> (((e3 +e (nat_e 1)) == e1) &&& (e3 =/= e4))) then
                  let x' := triple_vfresh (pi,sig) A in 
                    Some (
                    (((pi &&& (e3 =/= var_e x')) &&& (var_e x' == nat_e 0),
                    star (star s1 (star (lst (var_e x') e4) (singl e3 (var_e x'))))
                    (cell (e3 +e nat_e 1))), A)::
                    (((pi &&& (e3 =/= var_e x')) &&& (var_e x' =/= nat_e 0),
                    star (star s1 (star (lst (var_e x') e4) (singl e3 (var_e x'))))
                    (cell (e3 +e nat_e 1))), A)::
                    nil)
                else Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp)), A)::nil)
        | (singl e1 e2) => Some ((pi, star emp sig, A)::nil)
        | (cell e1) => Some ((pi, star emp sig, A)::nil)
        | (lst e1 e2) => Some ((pi, star emp sig, A)::nil)
        | _ => Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp)), A)::nil)
      end

  end.

Opaque entail_fct.  
Opaque remove_empty_heap.
Opaque star_assoc_left.

Lemma tritra_step'_correct: forall A pi sig l,
  tritra_step' pi sig A = Some l ->
  (forall pi' sig' A', 
    In ((pi',sig'),A') l -> 
    tritra (pi',sig') A'    
  ) ->
  tritra (pi,sig) A.

  destruct A; simpl; intros.

  generalize (entail_fct_correct a (pi, sig)  nil); intros.
  destruct (entail_fct (pi, sig) a nil); try discriminate.
  injection H; clear H; intros; subst l.
  eapply tritra_entail.
  apply H1; auto.

  destruct A.
  
  injection H; clear H; intros; subst l0.
  eapply tritra_subst_elt.
  eapply H0; simpl; left; auto.

  injection H; clear H; intros; subst l0.
  eapply tritra_subst_subst.
  eapply H0; simpl; left; auto.

  destruct sig.

  eapply tritra_precond_stre with (
    (pi, star emp (singl e0 e1))
  ).
  eapply entail_soundness; Entail.
  eapply H0.
  injection H; intros; subst l0.
  simpl; left; auto.

  eapply tritra_precond_stre with (
    (pi, star emp (cell e0))
  ).
  eapply entail_soundness; Entail.
  eapply H0.
  injection H; intros; subst l0.
  simpl; left; auto.
  
  eapply tritra_precond_stre with (
    pi,
    remove_empty_heap  pi
    (star_assoc_left (star_com emp) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply H0.
  injection H; intros; subst l0.
  simpl; left; auto.
  
  destruct sig2.

  generalize (expr_b_dp_correct (pi =b> e0 == subst_e_lst l e)); intros.
  destruct (expr_b_dp (pi =b> e0 == subst_e_lst l e)).
  injection H; clear H; intros; subst l0.
  eapply tritra_subst_lookup with (x' := (max (max (var_max_lst l) (var_max_wpAssrt A)) v + 1)).
  intros; generalize (H1 (refl_equal _) s); intros.
  unfold eval_pi; unfold eval_pi in H.
  Omega_exprb.
  red; simpl; repeat Resolve_ge_max.
  red; simpl; repeat Resolve_ge_max.
  red; simpl; repeat Resolve_ge_max.
  eapply H0; simpl; left; auto.

  clear H1.
  eapply tritra_precond_stre with (
    (pi,
         remove_empty_heap pi (star_assoc_left (star_com (star sig1 (singl e0 e1))) emp)
         )
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l0.
  simpl; left; auto.

  generalize (expr_b_dp_correct (pi =b> e0 == subst_e_lst l e)); intros.
  destruct (expr_b_dp (pi =b> e0 == subst_e_lst l e)).
  injection H; clear H; intros; subst l0.
  eapply tritra_subst_lookup2 with (x' := (max (max (var_max_lst l) (var_max_wpAssrt A)) v + 1)) (x'' := (max
                      (max (var_max_expr_b pi)
                         (var_max_Sigma (star sig1 (cell e0))))
                      (max (var_max_lst l) (var_max_wpAssrt (wpLookup v e A))) +
                    1)).
  intros; generalize (H1 (refl_equal _) s); intros.
  unfold eval_pi; unfold eval_pi in H.
  Omega_exprb.
  red; simpl; repeat Resolve_ge_max.
  red; simpl; repeat Resolve_ge_max.
  red; simpl; repeat Resolve_ge_max.
  red; simpl; repeat Resolve_ge_max.
  red; simpl; repeat Resolve_ge_max.
  eapply H0; simpl; left; auto.

  clear H1.
  eapply tritra_precond_stre with (
  pi,
         remove_empty_heap pi
           (star_assoc_left (star_com (star sig1 (cell e0))) emp)
    ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l0.
  simpl; left; auto.

  eapply tritra_precond_stre with (
     pi,
         remove_empty_heap pi (star_assoc_left (star_com (star sig1 emp)) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l0.
  simpl; left; auto.


  eapply tritra_precond_stre with (
     pi,
         remove_empty_heap pi (star_assoc_left (star_com (star sig1 (star sig2_1 sig2_2))) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l0.
  simpl; left; auto.

  generalize (expr_b_dp_correct (pi =b> (e0 =/= e1) &&& (e0 == subst_e_lst l e))); intros.
  destruct (expr_b_dp (pi =b> (e0 =/= e1) &&& (e0 == subst_e_lst l e))).
  eapply tritra_subst_lookup_lst with (x' :=
    triple_vfresh (pi, star sig1 (lst e0 e1)) (wpSubst l (wpLookup v e A))
  ).
  intros; generalize (H1 (refl_equal _) s); intros.
  unfold eval_pi; unfold eval_pi in H2.
  split; Omega_exprb.
  simpl.  
  auto.
  eapply H0.
  injection H; clear H; intros; subst l0.
  simpl; left; auto.
  eapply H0.
  injection H; clear H; intros; subst l0.
  simpl; right; left; auto.
  
  clear H1.

  generalize (expr_b_dp_correct (pi =b> (e0 =/= e1) &&& ((e0 +e nat_e 1) == subst_e_lst l e))); intros.
  destruct (expr_b_dp (pi =b> (e0 =/= e1) &&& ((e0 +e nat_e 1) == subst_e_lst l e))); try discriminate.
  eapply tritra_subst_lookup_lst' with (x' :=
    triple_vfresh (pi, star sig1 (lst e0 e1)) (wpSubst l (wpLookup v e A))
  ).
  intros; generalize (H1 (refl_equal _) s); intros.
  unfold eval_pi; unfold eval_pi in H2.
  split; Omega_exprb.
  simpl.  
  auto.
  eapply H0.
  injection H; clear H; intros; subst l0.
  simpl; left; auto.
  eapply H0.
  injection H; clear H; intros; subst l0.
  simpl; right; left; auto.

 clear H1.
  
  eapply tritra_precond_stre with (
     pi,
         remove_empty_heap pi (star_assoc_left (star_com (star sig1 (lst e0 e1))) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l0.
  simpl; left; auto.

  eapply tritra_precond_stre with (
    (pi, star emp (lst e0 e1))
  ).
  eapply entail_soundness; Entail.
  injection H; intros; subst l0.
  eapply H0.
  simpl; left; auto.
  
  eapply tritra_subst_mutation.
  injection H; intros; subst l0.
  eapply H0.
  simpl; left; auto.

  eapply tritra_subst_if.
  injection H; intros; subst l0.
  eapply H0.
  simpl; left; auto.
  
  destruct sig.
    
  eapply tritra_precond_stre with (
    (pi, star emp (singl e0 e1))
  ).
  eapply entail_soundness; Entail.
  eapply H0.
  injection H; intros; subst l.
  simpl; left; auto.
    
  eapply tritra_precond_stre with (
    (pi, star emp (cell e0))
  ).
  eapply entail_soundness; Entail.
  eapply H0.
  injection H; intros; subst l.
  simpl; left; auto.
  
  simpl in H.

  eapply tritra_precond_stre with (
     pi,
         remove_empty_heap pi (star_assoc_left emp emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply H0.
  injection H; intros; subst l.
  simpl; left; auto.
  
  destruct sig2.
  
  generalize (expr_b_dp_correct (pi =b>  (e0 == e))); intros.
  destruct (expr_b_dp (pi =b> (e0 == e))).
  eapply tritra_lookup.
  intros; generalize (H1 (refl_equal _) s); intros.
  unfold eval_pi; unfold eval_pi in H2.
  Omega_exprb.
  simpl; intuition.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.
    
  clear H1.

  eapply tritra_precond_stre with (
     pi,
         remove_empty_heap pi (star_assoc_left (star_com (star sig1 (singl e0 e1))) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.
  
  generalize (expr_b_dp_correct (pi =b> e0 == e)); intros.
  destruct (expr_b_dp (pi =b> e0 == e)).
  injection H; clear H; intros; subst l.
  eapply tritra_lookup' with (x' := (max
                     (max (var_max_expr_b pi)
                        (max (var_max_Sigma sig1) (var_max_expr e0)))
                     (max (max v (var_max_expr e)) (var_max_wpAssrt A)) + 1)).
  intros; generalize (H1 (refl_equal _) s); intros.
  unfold eval_pi; unfold eval_pi in H.
  Omega_exprb.
  red; simpl; repeat Resolve_ge_max.
  red; simpl; repeat Resolve_ge_max.
  eapply H0.
  simpl; left; auto.
  
  clear H1.

  eapply tritra_precond_stre with (
     pi,
         remove_empty_heap pi (star_assoc_left (star_com (star sig1 (cell e0))) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.
  
  eapply tritra_precond_stre with (
     pi,
         remove_empty_heap pi (star_assoc_left (star_com (star sig1 emp)) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.
  
  eapply tritra_precond_stre with (
     pi,
         remove_empty_heap pi (star_assoc_left (star_com (star sig1 (star sig2_1 sig2_2))) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.
  
  generalize (expr_b_dp_correct (pi =b> (e0 =/= e1) &&& (e0 == e))); intros.
  destruct (expr_b_dp (pi =b> (e0 =/= e1) &&& (e0 == e))); try discriminate.
  eapply tritra_lookup_lst.
  intros; generalize (H1 (refl_equal _) s); intros.
  unfold eval_pi; unfold eval_pi in H2.
  split; Omega_exprb.
  intuition.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; right; left; auto.
  
  clear H1.
  
  generalize (expr_b_dp_correct (pi =b> (e0 =/= e1) &&& ((e0 +e nat_e 1) == e))); intros.
  destruct (expr_b_dp (pi =b> (e0 =/= e1) &&& ((e0 +e nat_e 1) == e))); try discriminate.
  eapply tritra_lookup_lst'.
  intros; generalize (H1 (refl_equal _) s); intros.
  unfold eval_pi; unfold eval_pi in H2.
  split; Omega_exprb.
  intuition.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; right; left; auto.
  
  clear H1.
  
  eapply tritra_precond_stre with (
     pi,
         remove_empty_heap pi (star_assoc_left (star_com (star sig1 (lst e0 e1))) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.
    
  eapply tritra_precond_stre with (
    (pi, star emp (lst e0 e1))
  ).
  eapply entail_soundness; Entail.
  injection H; intros; subst l.
  eapply H0.
  simpl; left; auto.

  destruct sig.

  eapply tritra_precond_stre with (
    (pi, star emp (singl e1 e2))
  ).
  eapply entail_soundness; Entail.
  injection H; intros; subst l.
  eapply H0.
  simpl; left; auto.

  eapply tritra_precond_stre with (
    (pi, star emp (cell e1))
  ).
  eapply entail_soundness; Entail.
  injection H; intros; subst l.
  eapply H0.
  simpl; left; auto.

  eapply tritra_precond_stre with (
     pi,
         remove_empty_heap pi (star_assoc_left (star_com emp) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.

  destruct sig2.

  generalize (expr_b_dp_correct (pi =b> (e == e1))); intros.
  destruct (expr_b_dp (pi =b> (e == e1))); try discriminate.
  eapply tritra_mutation.
  intros; generalize (H1 (refl_equal _) s); intros.
  assert (s |b= e == e1).
  unfold eval_pi in H2.
  Omega_exprb.
  unfold eval_pi; unfold eval_pi in H2.
  Omega_exprb.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.

  clear H1.

  eapply tritra_precond_stre with (
    pi,
    remove_empty_heap pi
    (star_assoc_left (star_com (star sig1 (singl e1 e2))) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.

  generalize (expr_b_dp_correct (pi =b> (e == e1))); intros.
  destruct (expr_b_dp (pi =b> (e == e1))); try discriminate.
  eapply tritra_mutation'.
  intros; generalize (H1 (refl_equal _) s); intros.
  assert (s |b= e == e1).
  unfold eval_pi in H2.
  Omega_exprb.
  unfold eval_pi; unfold eval_pi in H2.
  Omega_exprb.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.

  eapply tritra_precond_stre with (
    pi,
    remove_empty_heap pi
    (star_assoc_left (star_com (star sig1 (cell e1))) emp)
  ).
  red; intros.
  inversion_clear H2; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H2.
  apply H2.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H5.
  apply H5.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.

  eapply tritra_precond_stre with (
    pi,
    remove_empty_heap pi
    (star_assoc_left (star_com (star sig1 emp)) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.

  eapply tritra_precond_stre with (
    pi,
    remove_empty_heap pi
    (star_assoc_left (star_com (star sig1 (star sig2_1 sig2_2)))
      emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.

  generalize (expr_b_dp_correct (pi =b> (e == e1) &&& (e1 =/= e2))); intros.
  destruct (expr_b_dp (pi =b> (e == e1) &&& (e1 =/= e2))); try discriminate.
  eapply tritra_mutation_lst.
  intros; generalize (H1 (refl_equal _) s); intros.
  unfold eval_pi; unfold eval_pi in H2.
  split; try Omega_exprb.
  assert (s |b= e == e1).
  Omega_exprb.
  Omega_exprb.
  intuition.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; right; left; auto.

  clear H1.

  generalize (expr_b_dp_correct (pi =b> ((e1 +e nat_e 1) == e) &&& (e1 =/= e2))); intros.
  destruct (expr_b_dp (pi =b> ((e1 +e nat_e 1) == e) &&& (e1 =/= e2))); try discriminate.
  eapply tritra_mutation_lst'.
  intros; generalize (H1 (refl_equal _) s); intros.
  unfold eval_pi; unfold eval_pi in H2.
  split; try Omega_exprb.
  intuition.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; right; left; auto.

  clear H1.

  eapply tritra_precond_stre with (
    pi,
    remove_empty_heap pi 
    (star_assoc_left (star_com (star sig1 (lst e1 e2))) emp)
  ).
  red; intros.
  inversion_clear H1; split; auto.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_assoc_left_correct'); intros.
  red in H1.
  apply H1.
  Compose_sepcon h heap.emp; auto.
  generalize (star_com_correct'); intros.
  red in H4.
  apply H4.
  auto.
  simpl; red; auto.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.
    
  eapply tritra_precond_stre with (
    (pi, star emp (lst e1 e2))
  ).
  eapply entail_soundness; Entail.
  injection H; intros; subst l.
  eapply H0.
  simpl; left; auto.

  eapply tritra_if.
  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; left; auto.

  eapply H0.
  injection H; clear H; intros; subst l.
  simpl; right; left; auto.
Qed.


Definition tritra_step (pi: Pi) (sig: Sigma) (A: wpAssrt) : option (list ((Pi * Sigma) * wpAssrt)) :=
  if expr_b_dp (!pi) then 
    Some nil 
    else 
      tritra_step' pi sig A.

Lemma tritra_step_correct: forall A pi sig l,
  tritra_step pi sig A = Some l ->
  (forall pi' sig' A', In ((pi', sig'),A') l -> tritra (pi', sig') A') ->
  tritra (pi, sig) A.
  intros.
  unfold tritra_step in H.
  generalize (expr_b_dp_correct (!pi)); intros.
  destruct (expr_b_dp (!pi)).
  eapply tritra_incons.
  intros.
  inversion_clear H2.
  generalize (H1 (refl_equal _) s); intros.
  unfold eval_pi in H3.
  simpl in H3.
  simpl in H2.
  rewrite H3 in H2.
  simpl in H2; discriminate.
  clear H1.
  eapply tritra_step'_correct.
  apply H.
  auto.
Qed.

Fixpoint tritra_list (l: list ((Pi * Sigma) * wpAssrt)) : option (list ((Pi * Sigma) * wpAssrt)) :=
  match l with
    | nil => Some nil
    | ((pi,sg), A)::tl =>
      match tritra_step pi sg A with
        | None => None
        | Some l' => 
          match tritra_list tl with
            | None => None
            | Some l'' => Some (l' ++ l'')
          end
      end
  end.

Lemma tritra_list_correct: forall l l',
  tritra_list l = Some l' ->
  (forall pi sig A, In ((pi, sig), A) l' -> tritra (pi, sig) A) ->    
  (forall pi sig A, In ((pi, sig), A) l -> tritra (pi, sig) A).
  
  induction l; simpl; intros; auto.
  contradiction.
  destruct a.
  destruct p.  
  generalize (tritra_step_correct w p s); intros.
  destruct (tritra_step p s w); try discriminate.
  generalize (H2 l0 (refl_equal _)); clear H2; intros.
  destruct (tritra_list l); try discriminate.
  generalize (IHl l1 (refl_equal _)); clear IHl; intros.
  injection H; clear H; intros; subst l'.
  inversion_clear H1.
  injection H; clear H; intros; subst p s w.
  eapply H2.
  intros.
  eapply H0.
  eapply in_or_app.
  left; auto.
  eapply H3.
  intros.
  eapply H0.
  eapply in_or_app.
  right; auto.
  auto.
Qed.

Fixpoint tritra_list_rec (l: list ((Pi * Sigma) * wpAssrt)) (size:nat) {struct size} : option (list ((Pi * Sigma) * wpAssrt)) :=
  match size with
    | 0 => Some l
    | S size' =>
      match tritra_list l with
        | None => None
        | Some l' => 
          match l' with
            | nil => Some nil
            | _ =>  tritra_list_rec l' size'
          end
      end
  end.

Lemma tritra_list_rec_correct : forall n l l',
  tritra_list_rec l n = Some l' ->
  (forall pi sig A, In ((pi,sig),A) l' -> tritra (pi,sig) A) ->    
  (forall pi sig A, In ((pi,sig),A) l -> tritra (pi,sig) A).
  induction n; simpl; intros; auto.
  injection H; intros; subst l.
  intuition.
  generalize (tritra_list_correct l); intros.
  destruct (tritra_list l); try discriminate.
  destruct l0.
  eapply H2.
  intuition.
  intros.
  simpl in H3; contradiction.
  auto.

  eapply H2; auto.
  intros.
  eapply IHn.
  apply H.
  apply H0.
  auto.
Qed.

Lemma tritra_list_rec_correct': forall n l,
  tritra_list_rec l n = Some nil ->
  (forall pi sig A, In ((pi,sig),A) l -> assrt_interp (pi,sig) ==> wpAssrt_interp A).
  intros.
  eapply tritra_soundness.
  eapply tritra_list_rec_correct.
  apply H.
  simpl; contradiction.
  auto.
Qed.

Fixpoint wpAssrt_size (A:wpAssrt) : nat :=
  match A with
    wpElt P => 2
    | wpSubst l P => 2 + wpAssrt_size P
    | wpLookup x e P => 2 + wpAssrt_size P
    | wpMutation e1 e2 P  => 2 + wpAssrt_size P
    | wpIf b L1 L2 => 2 + wpAssrt_size L1 + wpAssrt_size L2
  end.

Definition triple_transformation_complexity (pi: expr_b) (sig: Sigma) (L: wpAssrt) : nat :=
  (Expr_B_size pi) * (sigma_size sig) * (wpAssrt_size L).

(* entry point *)
Fixpoint triple_transformation (P: Assrt) (Q: wpAssrt) {struct P} : option (list ((Pi * Sigma) * wpAssrt)) :=
  match P with
    | nil => Some nil
    | (pi, sig) :: tl =>
      match tritra_list_rec 
        (((compute_constraints (cell_loc_not_null pi sig) sig, sig), Q)::nil) 
        (triple_transformation_complexity pi sig Q) with
        | Some l => 
          match triple_transformation tl Q with
            | Some l' => Some (l ++ l')
            | None => None
          end
        | None => 
          match triple_transformation tl Q with
            | Some l' => Some (((pi,sig),Q)::l')
            | None => None
          end
      end
  end.

Lemma triple_transformation_correct: forall P Q,
  triple_transformation P Q = Some nil  ->
  Assrt_interp P ==> wpAssrt_interp Q.
  induction P; simpl; red; intros; try contradiction.
  destruct a.
  generalize (tritra_list_rec_correct' (triple_transformation_complexity p s0 Q) ((compute_constraints (cell_loc_not_null p s0) s0, s0, Q) :: nil)); intros.
  destruct (tritra_list_rec ((compute_constraints (cell_loc_not_null p s0) s0, s0, Q) :: nil) (triple_transformation_complexity p s0 Q)); try discriminate.
  generalize (IHP Q); intros.
  red in H2.
  clear IHP.
  destruct (triple_transformation P Q); try discriminate.
  destruct l; destruct l0; try discriminate.
  inversion_clear H0.
  red in H1; eapply H1.
  auto.
  simpl; left; auto.
  generalize compute_constraints_correct; intros.
  red in H0; eapply H0; clear H0.
  generalize cell_loc_not_null_correct; intros.
  red in H0; eapply H0; clear H0.
  auto.
  eapply H2; auto.
  generalize (IHP Q); intros.
  red in H2.
  clear IHP.
  destruct (triple_transformation P Q); try discriminate.
Qed.

(*
Fixpoint triple_transformation (P: Assrt) (Q: wpAssrt) {struct P} : option (list ((Pi * Sigma) * wpAssrt)) :=
  match P with
    | nil => Some nil
    | (pi,sig)::tl =>
      match (tritra_list_rec (((pi,sig),Q)::nil) (triple_transformation_complexity pi sig Q)) with
        | Some l => 
          match triple_transformation tl Q with
            | Some l' => Some (l ++ l')
            | None => None
          end
        | None => 
          match triple_transformation tl Q with
            | Some l' => Some (((pi,sig),Q)::l')
            | None => None
          end

      end
  end.

Lemma triple_transformation_correct: forall P Q,
  triple_transformation P Q = Some nil  ->
  (Assrt_interp P) ==> (wpAssrt_interp Q).
  induction P; simpl; red; intros; try contradiction.
  destruct a.
  generalize (tritra_list_rec_correct' (triple_transformation_complexity p s0 Q) ((p, s0, Q) :: nil)); intros.
  destruct (tritra_list_rec ((p, s0, Q) :: nil) (triple_transformation_complexity p s0 Q)); try discriminate.
  generalize (IHP Q); intros.
  red in H2.
  clear IHP.
  destruct (triple_transformation P Q); try discriminate.
  destruct l; destruct l0; try discriminate.
  inversion_clear H0.
  red in H1; eapply H1.
  auto.
  simpl; left; auto.
  auto.
  eapply H2; auto.
  generalize (IHP Q); intros.
  red in H2.
  clear IHP.
  destruct (triple_transformation P Q); try discriminate.
Qed.
*)

Fixpoint triple_transformation2 (P: Assrt) (Q: wpAssrt) {struct P} : bool :=
  match P with
    | nil => true
    | (pi,sig)::tl =>
      match tritra_list_rec (((pi,sig),Q)::nil) (triple_transformation_complexity pi sig Q) with
        | Some nil => 
          triple_transformation2 tl Q 
        | _ => false
      end
  end.

Lemma triple_transformation2_correct: forall P Q,
  triple_transformation2 P Q = true  ->
  Assrt_interp P ==> wpAssrt_interp Q.
  induction P; simpl; red; intros; try contradiction.
  destruct a.
  generalize (tritra_list_rec_correct' (triple_transformation_complexity p s0 Q) ((p, s0, Q) :: nil)); intros.
  destruct (tritra_list_rec ((p, s0, Q) :: nil) (triple_transformation_complexity p s0 Q)); try discriminate.
  destruct l; try discriminate.
  inversion_clear H0.
  red in H1; eapply H1; auto.
  simpl; left; intuition.
  auto.
  red in IHP; eapply IHP; auto.
Qed.



  



