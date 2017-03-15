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

(* file outline:
 * 1. definition of syntactic constructs and proofs of their properties
 * 2. a module for fresh variables (w.r.t. syntactic constructs)
 * 3. definition of LWP and its soundness 
 * 4. weakest pre-condition generator and its soudness
 * 5. Resolution tactic 
 *)

Load seplog_header.

Require Import Omega.
Require Import Bool.

(*
 * definition of syntactic constructs
 *)

Definition Pi := expr_b.

Inductive Sigma : Set :=
  singl : expr -> expr -> Sigma
  | cell : expr -> Sigma
  | epsi : Sigma
  | star : Sigma -> Sigma -> Sigma.

Fixpoint Sigma_interp (a : Sigma) : assert :=
  match a with
    singl e1 e2 => e1 |-> e2
    | epsi => sep.emp
    | star s1 s2 => (Sigma_interp s1) ** (Sigma_interp s2)
    | cell e => (fun s h => exists v, (e |-> int_e v) s h)
  end.

Definition assrt := prod Pi Sigma.

Definition assrt_interp (a: assrt) : assert :=
   match a with
     (pi, sigm) => (fun s h => eval_b pi s = true /\ Sigma_interp sigm s h)
   end.

(* A proof system for assrt entailment *)

Inductive ps1 : assrt -> assrt -> Prop :=
  ps1_incons: forall pi1 pi2 sig1 sig2, 
    (forall s , eval_b pi1 s = true -> False) -> 
    ps1 (pi1,sig1) (pi2,sig2)

  | ps1_tauto: forall pi1 pi2, 
    (forall s , eval_b pi1 s = true -> eval_b pi2 s = true) -> 
    ps1 (pi1,epsi) (pi2,epsi)

  | ps1_coml: forall pi1 sig1 sig2 L,
    ps1 (pi1,star sig2 sig1) L ->
    ps1 (pi1,star sig1 sig2) L

  | ps1_comr: forall pi1 sig1 sig2 L,
    ps1 L (pi1,star sig2 sig1)  ->
    ps1 L (pi1,star sig1 sig2)

  | ps1_assocl: forall pi1 sig1 sig2 sig3 L,
    ps1 (pi1,star (star sig1 sig2) sig3) L ->
    ps1 (pi1,star sig1 (star sig2 sig3)) L

  | ps1_assocr: forall pi1 sig1 sig2 sig3 L,
    ps1 L (pi1,star (star sig1 sig2) sig3)  ->
    ps1 L (pi1,star sig1 (star sig2 sig3))

  | ps1_epseliml: forall pi1 sig1 L,
    ps1 (pi1,sig1) L ->
    ps1 (pi1,star sig1 epsi) L

  | ps1_epselimr: forall pi1 sig1 L,
    ps1  L (pi1,sig1) ->
    ps1  L (pi1,star sig1 epsi)

  | ps1_epsintrol: forall pi1 sig1 L,
    ps1 (pi1,star sig1 epsi) L ->
    ps1 (pi1,sig1) L

  | ps1_epsintror: forall pi1 sig1 L,
    ps1  L (pi1,star sig1 epsi) ->
    ps1  L (pi1,sig1)
    
  | ps1_star_elim: forall pi1 pi2 sig1 sig2 e1 e2 e3 e4,
    (forall s, eval_b pi1 s = true -> eval_b (e1 == e3) s = true) ->
    (forall s , eval_b pi1 s = true -> eval_b (e2 == e4) s = true) ->    
    ps1 (pi1,sig1) (pi2,sig2) ->
    ps1 (pi1,star sig1 (singl e1 e2)) (pi2, star sig2 (singl e3 e4))

  | ps1_star_elim': forall pi1 pi2 sig1 sig2 e1 e2 e3,
    (forall s, eval_b pi1 s = true -> eval_b (e1 == e3) s = true) ->
    ps1 (pi1,sig1) (pi2,sig2) ->
    ps1 (pi1,star sig1 (singl e1 e2)) (pi2, star sig2 (cell e3))
    
  | ps1_star_elim'': forall pi1 pi2 sig1 sig2 e1 e3,
    (forall s, eval_b pi1 s = true -> eval_b (e1 == e3) s = true) ->
    ps1 (pi1,sig1) (pi2,sig2) ->
    ps1 (pi1,star sig1 (cell e1)) (pi2, star sig2 (cell e3)).
    

(* Soundness of the proof system *)

Lemma ps1_soundness: forall P Q, ps1 P Q -> 
  (assrt_interp P) ==> (assrt_interp Q).
intros.
induction H.

red; simpl; intros.
generalize (H s (proj1 H0)); contradiction.

red; simpl; intros.
generalize (H s (proj1 H0)); intuition.

red; simpl; intros.
red in IHps1.
apply IHps1.
simpl.
inversion_clear H0.
split; [auto | rewrite sep.con_com_equiv; auto].

red; simpl; intros.
red in IHps1; simpl in IHps1.
rewrite sep.con_com_equiv.
apply IHps1; auto.

red; simpl; intros.
red in IHps1; simpl in IHps1.
rewrite <- sep.con_assoc_equiv in H0.
intuition.

red; simpl; intros.
red in IHps1; simpl in IHps1.
rewrite <- sep.con_assoc_equiv.
eapply IHps1; auto.

red; simpl; intros.
red in IHps1; simpl in IHps1.
eapply IHps1.
split; [apply (proj1 H0)| eapply (sep.con_emp (Sigma_interp sig1) s h); apply (proj2 H0)].

red; simpl; intros.
red in IHps1; simpl in IHps1.
generalize (IHps1 s h H0); intros.
split; [apply (proj1 H1)| eapply (sep.con_emp' (Sigma_interp sig1) s h); apply (proj2 H1)].

red; simpl; intros.
red in IHps1; simpl in IHps1.
eapply IHps1.
split; [apply (proj1 H0)| eapply (sep.con_emp' (Sigma_interp sig1) s h); apply (proj2 H0)].

red; simpl; intros.
red in IHps1; simpl in IHps1.
generalize (IHps1 s h H0); intros.
split; [apply (proj1 H1)| eapply (sep.con_emp (Sigma_interp sig1) s h); apply (proj2 H1)].

red; simpl; intros.
red in IHps1; simpl in IHps1.
inversion_clear H2.
Decompose_sepcon H4 h1 h2.
generalize (IHps1 s h1 (conj H3 H4)); intro X; inversion_clear X.
split.
auto.
Compose_sepcon h1 h2.
auto.
generalize (H s H3); generalize (H0 s H3); intros.
Mapsto.

red; simpl; intros.
red in IHps1; simpl in IHps1.
inversion_clear H1.
Decompose_sepcon H3 h1 h2.
generalize (IHps1 s h1 (conj H2 H3)); intro X; inversion_clear X.
split.
auto.
Compose_sepcon h1 h2.
auto.
generalize (H s H2); intros.
exists (eval e2 s).
Mapsto.

red; simpl; intros.
red in IHps1; simpl in IHps1.
inversion_clear H1.
Decompose_sepcon H3 h1 h2.
generalize (IHps1 s h1 (conj H2 H3)); intro X; inversion_clear X.
split.
auto.
Compose_sepcon h1 h2.
auto.
generalize (H s H2); intros.
inversion_clear H6.
exists x.
Mapsto.
Qed.

(* Tactics to prove a ps1 goal *)

Ltac ps1_turnl :=
  match goal with
      | |- ps1 (?Pi, cell ?e) ?L => eapply ps1_epsintrol; eapply ps1_coml; repeat eapply ps1_assocl
      | |- ps1 (?Pi, singl ?e1 ?e2) ?L => eapply ps1_epsintrol; eapply ps1_coml; repeat eapply ps1_assocl
      | |- ps1 (?Pi, star ?e1 ?e2) ?L => eapply ps1_coml; repeat eapply ps1_assocl
   end.

Ltac ps1_turnr :=
  match goal with
      | |- ps1 ?L (?Pi, cell ?e) => eapply ps1_epsintror; eapply ps1_comr; repeat eapply ps1_assocr
      | |- ps1 ?L (?Pi, singl ?e1 ?e2) => eapply ps1_epsintror; eapply ps1_comr; repeat eapply ps1_assocr
      | |- ps1 ?L (?Pi, star ?e1 ?e2) => eapply ps1_comr; repeat eapply ps1_assocr
   end.


Ltac ps1_resolve := repeat eapply ps1_assocr; repeat eapply ps1_assocl;
  match goal with 
    
    | |- ps1 (?pi1, star ?sig1 epsi) ?L => ps1_turnl; idtac
    | |- ps1 ?L (?Pi, cell ?e) => ps1_turnr; idtac
    | |- ps1 ?L (?Pi, singl ?e1 ?e2) => ps1_turnr; idtac
    | |- ps1 (?Pi, cell ?e) ?L => ps1_turnl; idtac
    | |- ps1 (?Pi, singl ?e1 ?e2) ?L => ps1_turnl; idtac
      
    | |- ps1 (?pi1, epsi) (?pi2, epsi) => eapply ps1_tauto; [intros; Omega_exprb]
    | |- ps1 (?pi1, epsi) (?pi2, epsi) => eapply ps1_incons; [intros; Omega_exprb]
      
  (*****)
      
    | |- ps1 (?pi1, star ?e epsi) ?L => eapply ps1_epseliml; idtac
    | |- ps1 ?L (?pi2, star ?e epsi) => eapply ps1_epselimr; idtac
      
  (*****)
      
    | |- ps1 (?pi1, star ?sig1 (singl ?e1 ?e2)) (?pi2, star ?sig2 (singl ?e3 ?e4)) => 
      (eapply ps1_star_elim; [ Omega_exprb | Omega_exprb | idtac] || ps1_turnl; idtac)
      
    | |- ps1 (?pi1, star ?sig1 (singl ?e1 ?e2)) (?pi2, star ?sig2 (cell ?e3)) => 
      (eapply ps1_star_elim'; [ Omega_exprb | idtac] || ps1_turnl; idtac)
      
    | |- ps1 (?pi1, star ?sig1 (cell ?e1)) (?pi2, star ?sig2 (cell ?e3)) => 
      (eapply ps1_star_elim''; [ Omega_exprb | idtac] || ps1_turnl; idtac)

    | |- ps1 (?pi2, star ?sig2 (cell ?e3)) (?pi1, star ?sig1 (singl ?e1 ?e2)) => ps1_turnl

   end.

Ltac ps1_Resolve := repeat ps1_resolve.

(* TODO: mettre des exemple (tirer de mery et/ou calcagno) *)
(*

Lemma ps1_ex1: forall vy vx,
ps1
     (true_b, star (singl (var_e 4) (int_e vx)) (singl (var_e 3) (int_e vy)))
     (true_b, star (singl (var_e 3) (int_e vy)) (singl (var_e 4) (int_e vx))).
  intros.
  ps1_resolve.
Qed.
*)

(*
Lemma ps1_ex2: forall startp sizep,
  startp > 0 -> sizep > 4 ->
  ps1
     (true_b,
     star
       (star (cell ((nat_e startp +e nat_e sizep) -e int_e 1%Z))
          (star (singl (nat_e startp) (int_e 1%Z))
             (singl (nat_e startp +e int_e 1%Z)
                ((int_e (Z_of_nat startp) +e int_e (Z_of_nat sizep)) -e
                 int_e 2%Z))))
       (cell ((nat_e startp +e nat_e sizep) -e int_e 2%Z)))
     (true_b,
     star
       (star
          (star (cell ((nat_e startp +e nat_e sizep) -e int_e 2%Z))
             (cell ((nat_e startp +e nat_e sizep) -e int_e 1%Z)))
          (singl (nat_e startp) (int_e 1%Z)))
       (singl (nat_e startp +e int_e 1%Z)
          ((int_e (Z_of_nat startp) +e int_e (Z_of_nat sizep)) -e int_e 2%Z))).

intros.

ps1_Resolve.

Qed.
*)



(* frag_decision is a certified decision procedure for entailment of assrt  *)

Require Import expr_b_dp.


Fixpoint Sigma_clean_epsi (t: Sigma) : Sigma :=
  match t with
    | star t1 t2 =>
      match (Sigma_clean_epsi t1) with
        | epsi => (Sigma_clean_epsi t2)
        | t1' => match (Sigma_clean_epsi t2) with
                 | epsi => t1'
                 | t2' => star t1' t2'
               end
      end
    | _ => t
  end.

Definition Sigma_elt_eq (e1 e2: Sigma) (env: Pi) : bool :=
  match (e1,e2) with
    (epsi,epsi) => true
    | ((singl x1 x2),(singl x3 x4)) => (andb (expr_b_dp (env =b> (x1 == x3))) (expr_b_dp (env =b> (x2 == x4))))
    | ((singl x1 x2),(cell x3)) => (expr_b_dp (env =b> (x1 == x3))) 
    | ((cell x1),(cell x3)) => (expr_b_dp (env =b> (x1 == x3))) 
    | (_,_) => false
  end.


Fixpoint Sigma_elt_term_extract (e t: Sigma) (env: Pi) {struct t}: option Sigma :=
  match t with
    | star t1 t2 =>
      match Sigma_elt_term_extract e t1 env with
        | None => match (Sigma_elt_term_extract e t2 env) with
                    | None => None
                    | Some t2' => Some (Sigma_clean_epsi (star t1 t2'))
                  end
        | Some t1' => Some (Sigma_clean_epsi (star t1' t2))
      end
    | _ => if (Sigma_elt_eq e t env) then Some epsi else None
  end.


Fixpoint Sigma_elt_term_extract' (e t: Sigma) (env: Pi) {struct t}: option Sigma :=
  match t with
    | star t1 t2 =>
      match Sigma_elt_term_extract' e t1 env with
        | None => match (Sigma_elt_term_extract' e t2 env) with
                    | None => None
                    | Some t2' => Some (Sigma_clean_epsi (star t1 t2'))
                  end
        | Some t1' => Some (Sigma_clean_epsi (star t1' t2))
      end
    | _ => if Sigma_elt_eq t e env then Some epsi else None
  end.


Fixpoint Sigma_term_term_eq (t1 t2: Sigma) (env: Pi) {struct t1}: option Sigma :=
  match t1 with
    | star t11 t12 =>
      match (Sigma_term_term_eq t11 t2 env) with
        | None => None 
        | Some t2' => match (Sigma_term_term_eq t12 t2' env) with
                        | None => None
                        | Some t2'' => Some t2''
                      end
      end
    | _ => match (Sigma_elt_term_extract t1 t2 env) with
               | None => None
               | Some t2' => Some t2'
             end
  end.

Fixpoint Sigma_get_cell_val (e: expr) (sig: Sigma) (env: Pi) {struct sig}: option expr :=
  match sig with
    | epsi => None
    | singl e1 e2 => if (expr_b_dp (env =b> (e1 == e))) then (Some e2) else None
    | (cell e1) => None
    | star s1 s2 =>
      match (Sigma_get_cell_val e s1 env) with
        | None => (Sigma_get_cell_val e s2 env)
        | Some e2 => Some e2
      end
  end.

Definition frag_decision (P Q: Pi * Sigma) : bool :=
  let (pi1,sig1) := P in
    ( let (pi2, sig2) := Q in
      (
        if (expr_b_dp (pi1 =b> pi2)) then
          match (Sigma_term_term_eq sig1 sig2 pi1) with
            | Some epsi => true
            | _ => false
          end
          else false
      )
    ).

Lemma Sigma_clean_epsi_correct: forall t,
  (Sigma_interp (Sigma_clean_epsi t) ==> Sigma_interp t).
  induction t; simpl; red; intros; auto.
  destruct (Sigma_clean_epsi t1); destruct (Sigma_clean_epsi t2); simpl in H; simpl.
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Compose_sepcon h heap.emp; [apply IHt1; auto | apply IHt2; simpl; red; auto].

  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Compose_sepcon h heap.emp; [apply IHt1; auto | apply IHt2; simpl; red; auto].

  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Compose_sepcon heap.emp h; [apply IHt1; simpl; red; auto | apply IHt2; auto].
  Compose_sepcon heap.emp h; [apply IHt1; simpl; red; auto | apply IHt2; auto].
  red in H; Compose_sepcon heap.emp heap.emp; [apply IHt1; simpl; red; auto | apply IHt2; simpl; red; auto].
  Compose_sepcon heap.emp h; [apply IHt1; simpl; red; auto | apply IHt2; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Compose_sepcon h heap.emp; [apply IHt1; auto | apply IHt2; simpl; red; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
Qed.

Lemma Sigma_clean_epsi_correct': forall t,
  (Sigma_interp t ==> Sigma_interp (Sigma_clean_epsi t)).
  induction t; simpl; red; intros; auto.
  destruct (Sigma_clean_epsi t1); destruct (Sigma_clean_epsi t2); simpl in H; simpl.
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  
  Decompose_sepcon H h1 h2; generalize (IHt2 _ _ H3); intros; simpl in H2; red in H2; subst h2; assert (h = h1); [Equal_heap | subst h1; apply IHt1; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Decompose_sepcon H h1 h2; generalize (IHt2 _ _ H3); intros; simpl in H2; red in H2;  subst h2; assert (h = h1); [Equal_heap | subst h1; apply IHt1; auto].
  
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Decompose_sepcon H h1 h2; generalize (IHt1 _ _ H0); intros; simpl in H2; red in H2; subst h1; assert (h = h2); [Equal_heap | subst h2; apply IHt2; auto].
  Decompose_sepcon H h1 h2; generalize (IHt1 _ _ H0); intros; simpl in H2; red in H2; subst h1; assert (h = h2); [Equal_heap | subst h2; apply IHt2; auto].
  red; auto.
  Decompose_sepcon H h1 h2.
  generalize (IHt1 _ _ H0); intros.
  generalize (IHt2 _ _ H3); intros.
  simpl in H2; simpl in H4.
  red in H2; red in H4.
  subst h1 h2.
  Equal_heap.
  Decompose_sepcon H h1 h2; generalize (IHt1 _ _ H0); intros; simpl in H2; red in H2; subst h1; assert (h = h2); [Equal_heap | subst h2; apply IHt2; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
  Decompose_sepcon H h1 h2; generalize (IHt2 _ _ H3); intros; simpl in H2; red in H2;  subst h2; assert (h = h1); [Equal_heap | subst h1; apply IHt1; auto].
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
Qed.


Lemma Sigma_elt_eq_correct: forall e1 e2 env,
  Sigma_elt_eq e1 e2 env = true ->
  (forall s h,
    (s |b= env) ->
    (Sigma_interp e1 s h -> Sigma_interp e2 s h)
  ).
destruct e1; destruct e2; simpl; intros; try discriminate.
unfold Sigma_elt_eq in H.
generalize (andb_prop _ _ H); intro X; inversion_clear X; clear H.
generalize (expr_b_dp_correct _ H2 s); intros.
generalize (expr_b_dp_correct _ H3 s); intros.
Mapsto.
exists (eval e0 s).
unfold Sigma_elt_eq in H.
generalize (expr_b_dp_correct _ H s); intros.
Mapsto.
inversion_clear H1.
exists x.
unfold Sigma_elt_eq in H.
generalize (expr_b_dp_correct _ H s); intros.
Mapsto.
auto.
Qed.

Opaque Sigma_clean_epsi.

Lemma Sigma_elt_term_extract_correct:
  forall e2 e1 env e2',
    Sigma_elt_term_extract e1 e2 env = Some e2' ->
    (forall s h,
       (s |b= env) ->
       (Sigma_interp (star e1 e2') s h -> Sigma_interp e2 s h)
    ).

  induction e2; simpl; intros.

  generalize (Sigma_elt_eq_correct e1 (singl e e0) env); intros.
  destruct (Sigma_elt_eq e1 (singl e e0) env); try discriminate.
  injection H; clear H; intros; subst e2'.
  simpl in H1.
  Decompose_sepcon H1 h1 h2.
  red in H5.
  subst h2.
  assert (h = h1); [Equal_heap | subst h1].
  apply (H2 (refl_equal true) s h H0); auto.

  generalize (Sigma_elt_eq_correct e1 (cell e) env); intros.
  destruct (Sigma_elt_eq e1 (cell e) env); try discriminate.
  injection H; clear H; intros; subst e2'.
  simpl in H1.
  Decompose_sepcon H1 h1 h2.
  red in H5.
  subst h2.
  assert (h = h1); [Equal_heap | subst h1].
  apply (H2 (refl_equal true) s h H0); auto.

  generalize (Sigma_elt_eq_correct e1 epsi env); intros.
  destruct (Sigma_elt_eq e1 epsi env); try discriminate.
  injection H; clear H; intros; subst e2'.
  simpl in H1.
  Decompose_sepcon H1 h1 h2.
  red in H5.
  subst h2.
  assert (h = h1); [Equal_heap | subst h1].
  apply (H2 (refl_equal true) s h H0); auto.

  generalize (IHe2_1 e1 env); intros.
  Decompose_sepcon H1 h1 h2.
  clear IHe2_1.
  destruct (Sigma_elt_term_extract e1 e2_1 env); try discriminate.
  injection H; clear H; intros; subst e2'.
  generalize (Sigma_clean_epsi_correct _ _ _ H6); intros.
  clear H6.
  simpl in H.
  Decompose_sepcon H h21 h22.
  Compose_sepcon (h1 +++ h21) h22; auto.
  apply (H2 s0 (refl_equal _) s (h1 +++ h21) H0).
  simpl.
  Compose_sepcon h1 h21; auto.
  clear H2.
  generalize (IHe2_2 e1 env); intros.
  destruct (Sigma_elt_term_extract e1 e2_2 env); try discriminate.
  injection H; clear H; intros; subst e2'.
  generalize (Sigma_clean_epsi_correct _ _ _ H6); intros.
  clear H6.
  simpl in H.
  Decompose_sepcon H h21 h22.
  Compose_sepcon h21 (h1 +++ h22).
  apply H5.
  apply (H2 s0 (refl_equal _) s (h1 +++ h22) H0).
  simpl.
  Compose_sepcon h1 h22; auto.
Qed.

Lemma Sigma_elt_term_extract'_correct:
  forall e2 e1 env e2',
    Sigma_elt_term_extract' e1 e2 env = Some e2' ->
    (forall s h,
       (s |b= env) ->
       Sigma_interp e2 s h ->
       Sigma_interp (star e1 e2') s h
    ).

  induction e2; simpl; intros.
  generalize (Sigma_elt_eq_correct (singl e e0) e1  env); intros.
  destruct (Sigma_elt_eq (singl e e0) e1 env); try discriminate.
  injection H; clear H; intros; subst e2'.
  simpl in H1.
  Compose_sepcon h heap.emp.
  apply H2; auto.
  simpl; red; auto.

  generalize (Sigma_elt_eq_correct (cell e) e1  env); intros.
  destruct (Sigma_elt_eq (cell e) e1 env); try discriminate.
  injection H; clear H; intros; subst e2'.
  simpl in H1.
  Compose_sepcon h heap.emp.
  apply H2; auto.
  simpl; red; auto.

  generalize (Sigma_elt_eq_correct epsi e1 env); intros.
  destruct (Sigma_elt_eq epsi e1 env); try discriminate.
  injection H; clear H; intros; subst e2'.
  simpl in H1.
  Compose_sepcon h heap.emp.
  apply H2; auto.
  simpl; red; auto.

  generalize (IHe2_1 e1 env); intros.
  Decompose_sepcon H1 h1 h2.
  clear IHe2_1.
  destruct (Sigma_elt_term_extract' e1 e2_1 env); try discriminate.
  injection H; clear H; intros; subst e2'.
  generalize (H2 s0 (refl_equal _) s h1 H0 H3); intros.
  simpl in H.
  Decompose_sepcon H h11 h12.
  Compose_sepcon h11  (h12 +++ h2); auto.
  apply Sigma_clean_epsi_correct'.
  Compose_sepcon h12 h2; auto.
  clear H2.
  generalize (IHe2_2 e1 env); intros.
  destruct (Sigma_elt_term_extract' e1 e2_2 env); try discriminate.
  injection H; clear H; intros; subst e2'.
  generalize (H2 s0 (refl_equal _) s h2 H0 H6); intros.
  simpl in H.
  Decompose_sepcon H h21 h22.
  Compose_sepcon h21 (h1 +++ h22); auto.
  apply Sigma_clean_epsi_correct'.
  Compose_sepcon h1 h22; auto.
Qed. 

Lemma Sigma_term_term_eq_correct: 
  forall t1 t2 env t1',
    (Sigma_term_term_eq t1 t2 env = Some t1') ->
    (forall s h,
      (s |b= env) ->
       (Sigma_interp (star t1 t1') s h -> Sigma_interp t2 s h)
    ).
  induction t1; simpl; intros.
  generalize (Sigma_elt_term_extract_correct t2 (singl e e0) env); intros.
  destruct (Sigma_elt_term_extract (singl e e0) t2 env); try discriminate.
  eapply (H2 s0 (refl_equal _ ) s h H0).
  inversion_clear H.
  simpl.
  Decompose_sepcon H1 h1 h2.
  Compose_sepcon h1 h2; auto.

  generalize (Sigma_elt_term_extract_correct t2 (cell e) env); intros.
  destruct (Sigma_elt_term_extract (cell e) t2 env); try discriminate.
  eapply (H2 s0 (refl_equal _ ) s h H0).
  inversion_clear H.
  simpl.
  Decompose_sepcon H1 h1 h2.
  Compose_sepcon h1 h2; auto.

  generalize (Sigma_elt_term_extract_correct t2 epsi env); intros.
  destruct (Sigma_elt_term_extract epsi t2 env); try discriminate.
  eapply (H2 s0 (refl_equal _ ) s h H0).
  inversion_clear H.
  simpl.
  Decompose_sepcon H1 h1 h2.
  Compose_sepcon h1 h2; auto.
  
  Decompose_sepcon H1 h1 h2.
  Decompose_sepcon H2 h11 h12.

  generalize (IHt1_1 t2 env); intros; clear IHt1_1.
  destruct (Sigma_term_term_eq t1_1 t2 env); try discriminate.
  apply (H7 s0 (refl_equal _) s h H0).
  simpl.
  Compose_sepcon h11 (h2 +++ h12); clear H3; auto.
  generalize (IHt1_2 s0 env); intros; clear IHt1_2.
  destruct (Sigma_term_term_eq t1_2 s0 env); try discriminate.
  eapply (H3 s1 (refl_equal _) s (h2 +++ h12) H0).
  inversion_clear H.
  simpl.
  Compose_sepcon h12 h2; auto.
Qed.


Lemma Sigma_get_cell_val_correct: forall sig e env e',
  Sigma_get_cell_val e sig env = Some e' ->
  (forall s h,
    (s |b= env) ->
    Sigma_interp sig s h -> (Sigma_interp (singl e e') ** TT) s h).
  induction sig.
  simpl.
  intros.
  assert (expr_b_dp (env =b> (e == e1)) = false \/ expr_b_dp (env =b> (e == e1)) = true).
  destruct (expr_b_dp (env =b> (e == e1))); intuition.
  inversion_clear H2.
  rewrite H3 in H.
  discriminate.
  rewrite H3 in H.  
  injection H; clear H; intros; subst e0.
  Compose_sepcon h heap.emp.
  Mapsto.
  generalize (expr_b_dp_correct _ H3 s); intros.
  Eval_b_hyp H.
  Eval_b_hyp H0.
  tauto.
  red; auto.
  
  simpl; intros; discriminate.

  simpl; intros; discriminate.

  simpl; intros.
  assert (Sigma_get_cell_val e sig1 env = None \/ exists v, Sigma_get_cell_val e sig1 env = Some v).
  destruct (Sigma_get_cell_val e sig1 env).
  right; exists e0; auto.
  left; auto.
  inversion_clear H2.
  rewrite H3 in H.
  assert (Sigma_get_cell_val e sig2 env = None \/ exists v, Sigma_get_cell_val e sig2 env = Some v).
  destruct (Sigma_get_cell_val e sig2 env).
  right; exists e0; auto.
  left; auto.
  inversion_clear H2.
  rewrite H4 in H; discriminate.
  inversion_clear H4.
  Decompose_sepcon H1 h1 h2.
  generalize (IHsig2 _ _ _ H2 _ _ H0 H7); intros.
  Decompose_sepcon H6 h21 h22.
  simpl in H8.
  Compose_sepcon h21 (h1 +++ h22).
  Mapsto.
  rewrite H2 in H; injection H; intros; subst x; auto.
  red; auto.
  inversion_clear H3.
  Decompose_sepcon H1 h1 h2.
  rewrite H2 in H.
  injection H; clear H; intros; subst x.
  generalize (IHsig1 _ _ _ H2 _ _ H0 H3); intros.
  Decompose_sepcon H h11 h12.
  Compose_sepcon h11 (h12 +++ h2).
  simpl in H7.
  auto.
  red; auto.
Qed.

Lemma frag_decision_correct: forall P Q,
  frag_decision P Q = true ->
  (assrt_interp P ==> assrt_interp Q).
  intros.
  red; intros.
  destruct P; destruct Q.
  simpl; simpl in H0.
  inversion_clear H0.
  unfold frag_decision in H.
  generalize (expr_b_dp_correct (p =b> p0)); intros.
  destruct (expr_b_dp (p =b> p0)); simpl in H; try discriminate.
  split.
  generalize (H0 (refl_equal true) s); intros; Omega_exprb.
  clear H0.
  generalize (Sigma_term_term_eq_correct s0 s1 p); intros.
  destruct (Sigma_term_term_eq s0 s1 p); simpl in H; try discriminate.
  eapply (H0 s2 (refl_equal (Some s2)) s h H1); clear H0.
  destruct s2; simpl in H; try discriminate.
  simpl.
  Compose_sepcon h heap.emp; [auto | red; auto].
Qed.

Transparent Sigma_clean_epsi.


(***********************************************************)

  (*  proof system for hoare triple using the fragment *)

(************************************************************)

Inductive L_assrt : Set :=
   L_elt : assrt -> L_assrt
   | L_subst : list (var.v * expr) -> L_assrt -> L_assrt
   | L_lookup : var.v -> expr -> L_assrt -> L_assrt
   | L_mutation : expr -> expr -> L_assrt -> L_assrt
   | L_if : expr_b -> L_assrt -> L_assrt -> L_assrt.

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

Fixpoint L_assrt_interp (a: L_assrt) : assert :=
  match a with
    L_elt a1 => assrt_interp a1
    | L_subst l L => subst_lst2update_store l (L_assrt_interp L)
    | L_lookup x e L => (fun s h => exists e0, (e |-> e0 ** (e |-> e0 -* (update_store2 x e0 (L_assrt_interp L)))) s h)
    | L_mutation e1 e2 L => (fun s h => exists e0, (e1 |-> e0 ** (e1 |-> e2 -* (L_assrt_interp L))) s h)
    | L_if b L1 L2 => (fun s h => (eval_b b s = true -> L_assrt_interp L1 s h) /\ 
      (eval_b b s = false -> L_assrt_interp L2 s h))
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
    | epsi => epsi
    | star s1 s2 => star (subst_Sigma s1 x e) (subst_Sigma s2 x e)
    | cell e1 => cell (subst_e e1 (var_e x) e)
  end.

Definition subst_assrt (a: assrt) (x: var.v) (e: expr): assrt :=
  match a with
    (pi, sigm) => (subst_b pi (var_e x) e, subst_Sigma sigm x e)
  end.

Fixpoint subst_assrt_lst (l:list (var.v * expr)) (a:assrt) {struct l} : assrt :=
  match l with 
    nil => a
    | (x,e)::tl => subst_assrt_lst tl (subst_assrt a x e)
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
  exists x0.
  repeat rewrite <- subst_e2store_update.
  auto.
  inversion_clear H.
  inversion_clear H0.
  exists x0.
  exists x1.
  repeat rewrite <- subst_e2store_update.
  auto.
  Decompose_sepcon H h1 h2.
  Compose_sepcon h1 h2.
  apply IHsigm1.
  auto.
  apply IHsigm2.
  auto.
Qed.

Lemma subst_Sigma2store_update': forall sigm s h x v,
  Sigma_interp sigm (store.update x (eval v s) s) h -> 
  Sigma_interp (subst_Sigma sigm x v) s h.
  induction sigm; simpl; intros; auto.
  inversion_clear H.
  exists x0.
  repeat rewrite subst_e2store_update.
  auto.
  inversion_clear H.
  inversion_clear H0.
  exists x0.
  exists x1.
  repeat rewrite subst_e2store_update.
  auto.
  Decompose_sepcon H h1 h2.
  Compose_sepcon h1 h2.
  apply IHsigm1.
  auto.
  apply IHsigm2.
  auto.
Qed.

Lemma subst_lst2update_store_assrt_interp: forall l s h pi sigm,
  assrt_interp (subst_assrt_lst l (pi, sigm)) s h ->
  subst_lst2update_store l (assrt_interp (pi, sigm)) s h.
  induction l; simpl; intros; auto.
  induction a; simpl.
  generalize (IHl _ _ _ _ H); intro.
  cutrewrite ( (update_store2 a b
        (fun (s0 : store.s) (h0 : heap.h) =>
          eval_b pi s0 = true /\ Sigma_interp sigm s0 h0)) =
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

Lemma subst_lst2update_store_subst_b_lst: forall (b':bool) l b s h,
  subst_lst2update_store l (fun s h => eval_b b s = b') s h ->
  eval_b (subst_b_lst l b) s = b'.
  induction l; simpl; intros; auto.
  induction a; simpl.
  apply IHl with h.
  unfold update_store2 in H.
  cutrewrite (
    (fun s0 (_ : heap.h) => eval_b (subst_b b (var_e a) b0) s0 = b') =
    (fun s (_ : heap.h) => eval_b b (store.update a (eval b0 s) s) = b')
  ).
  auto.
  apply sep.assert_ext.
  split; intros.
  rewrite <- subst_b2store_update; auto.
  rewrite subst_b2store_update; auto.
Qed.

(*
 * relations between "subst_lst2update_store" and logical connectives 
  (entailment, /\, ->, exists, sepcon, sepimp, mapsto) 
 *)

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
  
  Parameter fresh_L_assrt : var.v -> L_assrt -> Prop.
  
  Parameter fresh_lst_decompose : forall x hd0 hd1 tl, fresh_lst x ((hd0,hd1)::tl) -> 
    fresh_e x hd1 /\ x <> hd0 /\ fresh_lst x tl.
  
  Parameter fresh_e_var_e_neq : forall x y, fresh_e x (var_e y) -> x <> y.
  
  Parameter fresh_e_eval: forall e x v s, fresh_e x e ->
    eval e (store.update x v s) = eval e s.
  
  Parameter fresh_L_assrt_inde: forall L x , fresh_L_assrt x L ->
    inde (x::nil) (L_assrt_interp L).

End FRESH.

Require Import Max.

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
      | epsi => 0
      | star s1 s2 => max (var_max_Sigma s1) (var_max_Sigma s2)
      | cell e1 => var_max_expr e1
    end.

  Definition var_max_assrt (a: assrt) : var.v :=
    match a with
      (pi, sigm) => max (var_max_expr_b pi) (var_max_Sigma sigm)
    end.

  Fixpoint var_max_lst (l: list (var.v * expr)) : var.v :=
    match l with 
      nil => 0
      | (v,e)::tl => max (max v (var_max_expr e)) (var_max_lst tl)
    end.

  Fixpoint var_max_L_assrt (a: L_assrt) : var.v :=
    match a with
      L_elt a1 => var_max_assrt a1
      | L_subst l L => max (var_max_lst l) (var_max_L_assrt L)
      | L_lookup x e L=> max (max x (var_max_expr e)) (var_max_L_assrt L)
      | L_mutation e1 e2 L => max (max (var_max_expr e1) (var_max_expr e2)) (var_max_L_assrt L)
      | L_if b L1 L2 => max (max (var_max_L_assrt L1) (var_max_L_assrt L2)) (var_max_expr_b b)
    end.

  Definition fresh_e x e := (x > var_max_expr e).

  Definition fresh_b x b := (x > var_max_expr_b b).

  Definition fresh_Sigma x s := (x > var_max_Sigma s).

  Definition fresh_assrt x a := (x > var_max_assrt a).

  Definition fresh_lst x l := (x > var_max_lst l).

  Definition fresh_L_assrt x L := (x > var_max_L_assrt L).

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
      | id: fresh_e _ _ |- _ => red in id; simpl in id; Max_inf_clean_hyp
      | id: fresh_b _ _ |- _ => red in id; simpl in id; Max_inf_clean_hyp
      | id: fresh_Sigma _ _ |- _ => red in id; simpl in id; Max_inf_clean_hyp
      | id: fresh_assrt _ _ |- _ => red in id; simpl in id; Max_inf_clean_hyp
      | id: fresh_lst _ _ |- _ => red in id; simpl in id; Max_inf_clean_hyp
      | id: fresh_L_assrt _ _ |- _ => red in id; simpl in id; Max_inf_clean_hyp
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
      | |- fresh_lst _ _ => red; simpl; Max_inf_resolve_goal
      | |- fresh_L_assrt _ _ => red; simpl; Max_inf_resolve_goal
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
    red.
    red in H1.
    inversion_clear H1.
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
    red.
    red in H1.
    inversion_clear H1.
    exists x1.
    split.
    rewrite fresh_e_eval in H2.
    intuition.
    simpl in H0.
    Max_inf_resolve.
    inversion_clear H2.
    rewrite fresh_e_eval in H3.
    intuition.
    simpl in H0.
    Max_inf_resolve.
    red; simpl; split; intros.
    inversion_clear H1.
    exists x1.
    red.
    red in H2.
    inversion_clear H2.
    exists x2.
    split.
    rewrite fresh_e_eval.
    intuition.
    Max_inf_resolve.
    rewrite fresh_e_eval.
    intuition.
    Max_inf_resolve.
    inversion_clear H1.
    exists x1.
    red.
    red in H2.
    inversion_clear H2.
    exists x2.
    rewrite fresh_e_eval in H1.
    rewrite fresh_e_eval in H1.
    split.
    intuition.
    intuition.
    Max_inf_resolve.
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

  Lemma fresh_L_assrt_inde: forall L x ,
    fresh_L_assrt x L ->
    inde (x::nil) (L_assrt_interp L).
    induction L.
    simpl.
    red; simpl; split; intros.
    generalize (fresh_assrt_inde a x H s h x0 v H0); intros.
    intuition.
    generalize (fresh_assrt_inde a x H s h x0 v H0); intros.
    intuition.
    red; simpl; split; intros.
    assert (inde (x::nil) (L_assrt_interp L)).
    eapply IHL.
    Max_inf_resolve.
    assert (x > var_max_lst l).
    Max_inf_resolve.
    generalize (fresh_lst_inde _ _ _ H2 H3 s h x0 v H0); intro X; inversion_clear X.
    intuition.
    assert (inde (x::nil) (L_assrt_interp L)).
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
    assert (x > var_max_L_assrt L).
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
    assert (x > var_max_L_assrt L).
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
    assert (x > var_max_L_assrt L).
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
    assert (x > var_max_L_assrt L).
    Max_inf_resolve.
    generalize (IHL _ H10 s h' x0 v H0); intro X; inversion_clear X.
    intuition.
    red; simpl; split; intros.
    inversion_clear H1.
    split.
    intros.
    assert (x > var_max_L_assrt L1).
    Max_inf_resolve.
    generalize (IHL1 _ H4 s h x0 v H0); intro X; inversion_clear X.
    eapply H5.
    eapply H2.
    assert (x > var_max_expr_b e).
    Max_inf_resolve.
    generalize (fresh_b_inde e x true H7 s h x0 v H0); intro X; inversion_clear X.
    intuition.
    intros.
    assert (x > var_max_L_assrt L2).
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
    assert (x > var_max_L_assrt L1).
    Max_inf_resolve.
    generalize (IHL1 _ H4 s h x0 v H0); intro X; inversion_clear X.
    eapply H6.
    eapply H2.
    assert (x > var_max_expr_b e).
    Max_inf_resolve.
    generalize (fresh_b_inde e x true H7 s h x0 v H0); intro X; inversion_clear X.
    intuition.
    intros.
    assert (x > var_max_L_assrt L2).
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

(*
 * definition of LWP and its soundness 
 * (note: j'ai vire incons, mais faut rajouter un equiv) 
 *)

Inductive LWP : assrt -> L_assrt -> Prop :=
  | LWP_entail: forall pi1 pi2 sig1 sig2, 
    (assrt_interp (pi1,sig1)) ==> (assrt_interp (pi2,sig2)) -> 
    LWP (pi1,sig1) (L_elt (pi2,sig2))

  | LWP_precond_stre: forall L1 L1' L2,
    (assrt_interp L1) ==> (assrt_interp L1') -> 
    LWP L1' L2 ->
    LWP L1 L2

  | LWP_if: forall pi1 sig1 L1 L2 b,
    LWP (pi1 &&& b,sig1)  L1 ->
    LWP (pi1 &&& (neg_b b),sig1) L2 ->
    LWP (pi1,sig1) (L_if b L1 L2)

  | LWP_mutation: forall pi1 sig1 e1 e2 e3 e4 L, 
    (forall s, eval_b pi1 s = true -> eval_b (e1 == e3) s = true) ->
    LWP (pi1,star sig1 (singl e1 e4)) L ->
    LWP (pi1,star sig1 (singl e1 e2)) (L_mutation e3 e4 L)
    
  | LWP_mutation': forall pi1 sig1 e1 e3 e4 L, 
    (forall s, eval_b pi1 s = true -> eval_b (e1 == e3) s = true) ->
    LWP (pi1,star sig1 (singl e1 e4)) L ->
    LWP (pi1,star sig1 (cell e1)) (L_mutation e3 e4 L)

  | LWP_lookup: forall pi1 sig1 e1 e2 e x L, 
    (forall s, eval_b pi1 s = true -> eval_b (e1 == e) s = true) ->
    LWP (pi1,star sig1 (singl e1 e2)) (L_subst ((x,e2)::nil) L) ->
    LWP (pi1,star sig1 (singl e1 e2)) (L_lookup x e L)

  | LWP_subst_elt: forall pi1 pi2 sig1 sig2 l, 
    LWP (pi1,sig1) (L_elt (subst_assrt_lst l (pi2,sig2))) ->
    LWP (pi1,sig1) (L_subst l (L_elt (pi2,sig2)))
    
  | LWP_subst_subst: forall pi1 sig1 l1 l2 L, 
    LWP (pi1,sig1) (L_subst (l2 ++ l1) L) ->
    LWP (pi1,sig1) (L_subst l1 (L_subst l2 L))
    
  | LWP_subst_lookup: forall pi1 sig1 e1 e2 e x x' l L,
    (forall s, eval_b pi1 s = true -> eval_b (e1 == (subst_e_lst l e)) s = true) ->                     
    fresh_lst x' l ->
    fresh_L_assrt x' L ->
    fresh_e x' (var_e x) ->
    LWP (pi1,star sig1 (singl e1 e2)) (L_subst ((x,(var_e x'))::l ++ ((x',e2)::nil)) L) ->
    LWP (pi1,star sig1 (singl e1 e2)) (L_subst l (L_lookup x e L))
    
  | LWP_subst_mutation: forall pi1 sig1 e1 e2 l L, 
    LWP (pi1,sig1) (L_mutation (subst_e_lst l e1) (subst_e_lst l e2) (L_subst l L)) ->
    LWP (pi1,sig1) (L_subst l (L_mutation e1 e2 L))

  | LWP_subst_if: forall pi1 sig1 l b L1 L2, 
    LWP (pi1,sig1)  (L_if (subst_b_lst l b) (L_subst l L1) (L_subst l L2)) ->
    LWP (pi1,sig1) (L_subst l (L_if b L1 L2)).

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
   fresh_lst x' l -> fresh_L_assrt x' L -> fresh_e x' (var_e x) ->
   subst_lst2update_store 
	l (fun s' h' => L_assrt_interp L (store.update x (eval (var_e x') s') s') h') (store.update x' (eval e s) s) h ->
   subst_lst2update_store 
	l (fun s' h' => L_assrt_interp L (store.update x (eval e s) s') h') s h.
  intros.
  eapply intro_fresh_var' with x'.
  auto.
  auto.
  eapply fresh_L_assrt_inde.
  auto.
  auto.
Qed.


Lemma LWP_soundness: forall P Q, LWP P Q -> 
  (assrt_interp P) ==> (L_assrt_interp Q).
intros.
induction H.

red; simpl; intros.
red in H; simpl in H.
apply H; auto.

red; intros.
apply IHLWP.
apply H.
auto.

red; simpl; intros.
red in IHLWP1; simpl in IHLWP1.
red in IHLWP2; simpl in IHLWP2.
split.
intuition.
intros.
eapply IHLWP2.
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
red in IHLWP.
simpl in IHLWP.
exists e2.
generalize (H _ H2); intros.
Compose_sepcon h2 h1.
Mapsto.
Intro_sepimp h2'  h'.
eapply IHLWP.
split; auto.
Compose_sepcon h1 h2'.
auto.
Mapsto.

red; simpl; intros.
red in IHLWP; simpl in IHLWP.
inversion_clear H1.
Decompose_sepcon H3 h1 h2.
generalize (H _ H2); intros.
inversion_clear H6.
exists (int_e x).
Compose_sepcon h2 h1.
Mapsto.
Intro_sepimp h2' h'.
eapply IHLWP.
split; auto.
Compose_sepcon h1 h2'.
auto.
Mapsto.

red; simpl; intros.
red in IHLWP; simpl in IHLWP.
inversion_clear H1.
generalize (H _ H2); intros.
Decompose_sepcon H3 h1 h2.
exists e2.
Compose_sepcon h2 h1.
Mapsto.
Intro_sepimp h2' h'.
eapply IHLWP.
split; auto.
Compose_sepcon h1 h2'.
auto.
Mapsto.

(* case LWP_subst_elt *)

red; simpl; intros.
red in IHLWP; simpl in IHLWP.
generalize (IHLWP _ _ H0); intros.
eapply (subst_lst2update_store_and' l (fun s h => eval_b pi2 s = true) (fun s h => Sigma_interp sig2 s h)  s h ).
generalize (subst_lst2update_store_assrt_interp l s h pi2 sig2 H1); intro.
generalize (subst_lst2update_store_and l (fun s h => eval_b pi2 s = true) (fun s h => Sigma_interp sig2 s h) s h H2); intros.
inversion_clear H3.
auto.

(* case LWP_subst_subst *)

red; simpl; intros.
red in IHLWP; simpl in IHLWP.
generalize (IHLWP _ _ H0); intros.
apply subst_lst2update_store_app.
auto.

(* case LWP_subst_lookup *)

red; simpl; intros.
red in IHLWP; simpl in IHLWP.
generalize (IHLWP _ _ H4); intros.
generalize (H _  (proj1 H4)); intros.
inversion_clear H4.
Decompose_sepcon H8 h1 h2.
apply (subst_lst2update_store_exists l 
  (fun e0 s h => (e |-> e0 ** (e |-> e0 -* update_store2 x e0 (L_assrt_interp L))) s h) 
  s h).

exists (int_e (eval e2 s)).

assert (
  (fun s0 h0 => 
    (e |-> int_e (eval e2 s) ** (e |-> int_e (eval e2 s) -* update_store2 x (int_e (eval e2 s)) (L_assrt_interp L))) s0 h0)
  = 
  (e |-> int_e (eval e2 s) ** (e |-> int_e (eval e2 s) -* update_store2 x (int_e (eval e2 s)) (L_assrt_interp L)))
).
apply sep.assert_ext.
red.
intuition.
rewrite H10; clear H10.

apply subst_lst2update_store_sep_con.
Compose_sepcon h2 h1.
apply subst_lst2update_store_mapsto.
Mapsto.
rewrite subst_e_lst_int_e; auto.

apply subst_lst2update_store_sepimp.
Intro_sepimp h2' h'.
unfold update_store2.
simpl.

assert (h2 = h2').
eapply singleton_equal.
apply H11.
generalize (subst_lst2update_store_mapsto' _ _ _ _ _ H12); intros.
apply H14.
Omega_exprb.
rewrite subst_e_lst_int_e; auto.
subst h2'.

assert (h = h').
Equal_heap.
subst h'.

rewrite <- H14.
generalize (subst_lst2update_store' _ _ _ _ _ _ H5); intro.
unfold update_store2 in H13.
apply intro_fresh_var with x'; auto.

(* case LWP_subst_mutation *)

red; simpl; intros.
red in IHLWP; simpl in IHLWP.
generalize (IHLWP _ _ H0); intros.
eapply subst_lst2update_store_lookup.
auto.

(* case LWP_subst_if *)

red; simpl; intros.
red in IHLWP; simpl in IHLWP.
generalize (IHLWP _ _ H0); intros.
inversion_clear H1.
apply (subst_lst2update_store_and' l (fun s0 h0 => eval_b b s0 = true -> L_assrt_interp L1 s0 h0) (fun s0 => fun h0 =>  eval_b b s0 = false -> L_assrt_interp L2 s0 h0) s h).
split.
apply (subst_lst2update_store_imply l (fun s => fun h => eval_b b s = true) (fun s => fun h => L_assrt_interp L1 s h) s h).
intros.
generalize (H2 (subst_lst2update_store_subst_b_lst true _ _ _ _ H1)); intros.
assert (L_assrt_interp L1 = (fun s => fun h => L_assrt_interp L1 s h)).
eapply sep.assert_ext.
red; simpl.
tauto.
rewrite <- H5.
auto.
apply (subst_lst2update_store_imply l (fun s => fun h => eval_b b s = false) (fun s => fun h => L_assrt_interp L2 s h) s h).
intros.
generalize (H3 (subst_lst2update_store_subst_b_lst false _ _ _ _ H1)); intros.
assert (L_assrt_interp L2 = (fun s => fun h => L_assrt_interp L2 s h)).
eapply sep.assert_ext.
red; simpl.
tauto.
rewrite <- H5.
auto.
Qed.

(*
 * weakest pre-condition generator and its soudness
 *)
  
Fixpoint wp_frag (Q: option L_assrt) (c: cmd) {struct c}: option L_assrt :=
  match c with 
    skip => match Q with 
              None => None
              | Some Q' => Some Q'
            end
    | assign v e => match Q with 
                            None => None
                            | Some Q' => Some (L_subst ((v,e)::nil) Q')
                          end
    | lookup v e => match Q with 
                                 None => None
                                 | Some Q' => Some (L_lookup v e Q')
			       end
    | mutation e1 e2 => match Q with 
                                    None => None
                                    | Some Q' => Some (L_mutation e1 e2 Q')
				  end
    | seq c1 c2 => wp_frag (wp_frag Q c2) c1 
    | ifte b thendo c1 elsedo c2 => match (wp_frag Q c1) with 
                                      None => None
                                      | Some Q1 => match (wp_frag Q c2) with 
                                                     None => None
                                                     | Some Q2 => Some (L_if b (Q1) (Q2))
                                                   end
                                    end
    | while a c => None
    | malloc v e => None
    | free e => None
  end.

Lemma wp_frag_None_is_None: forall c,  wp_frag None c = None.
  induction c; simpl; auto.
  rewrite IHc2.
  auto.
  rewrite IHc1.
  auto.
Qed.

Lemma wp_frag_soudness: forall c Q Q', 
  wp_frag (Some Q) c = Some Q' -> {{ L_assrt_interp Q' }} c {{ L_assrt_interp Q }}.
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
  eapply semax_seq with (L_assrt_interp x).
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
  apply semax_strengthen_pre with (L_assrt_interp x).
  red.
  tauto.
  eapply IHc1.
  auto.
  apply semax_strengthen_pre with (L_assrt_interp x0).
  red.
  tauto.
  eapply IHc2.
  auto.
  rewrite H2 in H.
  inversion H.
  rewrite H1 in H; inversion H.
Qed.

(*
 * Resolution tactic 
 *)

Lemma LWP_use: forall c P Q R, 
  wp_frag (Some (L_elt Q)) c = Some R -> 
  LWP P R -> 
  {{ assrt_interp P }} c {{ assrt_interp Q }}.
  intros.
  generalize (wp_frag_soudness _ _ _ H); intros.
  simpl in H1.
  eapply semax_strengthen_pre with (L_assrt_interp R); [apply LWP_soundness; auto | auto].
Qed.

(* the following lemma replaces the constructor LWP_subst_lookup in the tactic,
  the difference is that it introduces a way to compute fresh variables *)
Lemma LWP_subst_lookup' : forall pi1 sig1 e1 e2 e x x' l L,
  (forall s,eval_b pi1 s = true -> (eval_b (e1 == (subst_e_lst l e))) s = true) ->                     
  x' = (max (max (var_max_lst l) (var_max_L_assrt L)) x) + 1 ->
  LWP (pi1,star sig1 (singl e1 e2)) (L_subst ((x,(var_e x'))::l ++ ((x',e2)::nil)) L) ->
  LWP (pi1,star sig1 (singl e1 e2)) (L_subst l (L_lookup x e L)).
  intros.
  apply LWP_subst_lookup with x'.
  auto.
  red.
  rewrite H0.
  assert (max (max (var_max_lst l) (var_max_L_assrt L)) x >= var_max_lst l).
  apply max_lemma5.
  apply max_lemma4.
  omega.
  red.
  rewrite H0.
  assert (max (max (var_max_lst l) (var_max_L_assrt L)) x >= var_max_L_assrt L).
  apply max_lemma5.
  apply max_lemma6.
  omega.
  omega.
  red.
  rewrite H0.
  simpl.
  assert (max (max (var_max_lst l) (var_max_L_assrt L)) x >= x).
  apply max_lemma6.
  omega.
  omega.
  auto.
Qed.

(********************************)
(* Tactics to resolve LWP goals *)
(********************************)

Fixpoint Sigma_assoc_left (t t': Sigma) {struct t}: Sigma :=
  match t with
    star sig1 sig2 => Sigma_assoc_left (sig2) (star t' sig1)
    | _ => match t' with
             epsi => t
             | _ => star t' t
           end
 end.

Definition Sigma_com (t: Sigma) : Sigma :=
  match t with
    star sig1 sig2 => star sig2 sig1
    | _ => t
  end.

Ltac Rotate_LWP_sig_lhs :=
  match goal with
    | |- LWP (?pi,?sig) ?L' =>
      eapply LWP_precond_stre with (
        (pi, Sigma_clean_epsi (Sigma_assoc_left (Sigma_com sig) epsi))
      ); [apply ps1_soundness; simpl; ps1_Resolve| simpl]
  end.

Ltac LWP_resolve := 
  match goal with 
    
    | |- LWP (?pi1, ?sig1) (L_elt (?pi2, ?sig2)) => eapply LWP_entail; [eapply ps1_soundness; ps1_Resolve]
      
    | |- LWP (?pi1, star ?sig1 (singl ?e1 ?e2)) (L_mutation ?e3 ?e4 ?L') => 
      (eapply LWP_mutation; [Omega_exprb | LWP_resolve] || Rotate_LWP_sig_lhs; idtac)
      
    | |- LWP (?pi1, star ?sig1 (cell ?e1)) (L_mutation ?e3 ?e4 ?L') => 
      (eapply LWP_mutation'; [Omega_exprb | LWP_resolve] || Rotate_LWP_sig_lhs; idtac)
      
    | |- LWP (?pi1, star ?sig1 (singl ?e1 ?e2)) (L_lookup ?x ?e ?L') => 
      (eapply LWP_lookup; [Omega_exprb | LWP_resolve] || Rotate_LWP_sig_lhs; idtac)
      
    | |- LWP ?L (L_subst ?l (L_elt ?L')) => eapply LWP_subst_elt; simpl; idtac
    | |- LWP ?L (L_subst ?l (L_subst ?l' ?L')) => eapply LWP_subst_subst; simpl; idtac
      
    | |- LWP ?L (L_subst ?l (L_lookup ?x ?e ?L')) => 
      (eapply LWP_subst_lookup'; [Omega_exprb | simpl; intuition | LWP_resolve] || Rotate_LWP_sig_lhs; idtac)
      
    | |- LWP ?L (L_subst ?l (L_mutation ?e1 ?e2 ?L')) => eapply LWP_subst_mutation; simpl; idtac
    | |- LWP ?L (L_subst ?l (L_if ?b ?L1 ?L2)) => eapply LWP_subst_if; simpl; idtac
    | |- LWP ?L (L_if ?b ?L1 ?L2) => eapply LWP_if; simpl; idtac
      
   end.

Ltac LWP_Resolve := Rotate_LWP_sig_lhs; repeat LWP_resolve.

Definition LWP_step (pi: Pi) (sig: Sigma) (A: L_assrt) : option (list ((Pi * Sigma) * L_assrt)) :=
  match A with
    | L_elt L => 
      if (frag_decision (pi,sig) L) then
        Some nil else None
    | L_subst l L =>
      match L with
        | L_elt L' => Some (((pi,sig), L_elt (subst_assrt_lst l L'))::nil) 
        | L_subst l' L' => Some (((pi,sig), L_subst (l'++ l) L')::nil)
        | L_lookup x e L' => 
          match (Sigma_get_cell_val (subst_e_lst l e) sig pi) with
            | None => None
            | Some e' => 
              let   x' := (max (max (var_max_lst l) (var_max_L_assrt L')) x) + 1 in (
                Some (((pi,sig),(L_subst ((x,(var_e x'))::l ++ ((x',e')::nil)) L'))::nil)
              )
          end
        | L_mutation e1 e2 L' => 
          Some (((pi,sig),(L_mutation (subst_e_lst l e1) (subst_e_lst l e2) (L_subst l L')))::nil)
        | L_if b L1 L2 => 
          Some (((pi,sig), L_if (subst_b_lst l b) (L_subst l L1) (L_subst l L2))::nil)
      end
    | L_lookup x e L =>       
      match (Sigma_get_cell_val e sig pi) with
        | None => None
        | Some e' => Some (((pi,sig),(L_subst ((x,e')::nil) L))::nil)
      end
    | L_mutation e1 e2 L => 
      match (Sigma_elt_term_extract' (cell e1) sig pi) with
        | None => None
        | Some sig' => Some (((pi,star (singl e1 e2) sig'),L)::nil)
      end
    | L_if b L1 L2 => 
      Some (((pi &&& b,sig),L1)::((pi &&& (! b),sig),L2)::nil)
  end.

Fixpoint L_assrt_size (A: L_assrt) : nat :=
  match A with
    L_elt P => 2
    | L_subst l P => 2 + L_assrt_size P
    | L_lookup x e P => 2 + L_assrt_size P
    | L_mutation e1 e2 P  => 2 + L_assrt_size P
    | L_if b L1 L2 => 2 + L_assrt_size L1 + L_assrt_size L2
  end.

Fixpoint LWP_list (l: (list ((Pi * Sigma) * L_assrt))) : option (list ((Pi * Sigma) * L_assrt)) :=
  match l with
    | nil => Some nil
    | ((pi,sig),A)::tl =>
      match (LWP_step pi sig A) with
        | None => None
        | Some l' => 
          match (LWP_list tl) with
            | None => None
            | Some l'' => Some (l' ++ l'')
          end
      end
  end.

Fixpoint LWP_list_rec (l: (list ((Pi * Sigma) * L_assrt))) (size: nat) {struct size}: option (list ((Pi * Sigma) * L_assrt)) :=
  match size with
    | 0 => Some l
    | S size' =>
      match (LWP_list l) with
        | None => None
        | Some l' => LWP_list_rec l' size'
      end
  end.
  

Definition frag_hoare (P Q: Pi * Sigma) (c: cmd) : bool :=
  match (wp_frag (Some (L_elt Q)) c) with
    | None => false
    | Some L =>
      let (p,s) := P in (
        match (LWP_list_rec (((p,s),L)::nil) (L_assrt_size L)) with
          | Some nil => true
          | _ => false
        end
      )
  end.

Opaque frag_decision.

Lemma LWP_step_correct: forall pi sig A l,
  LWP_step pi sig A = Some l ->
  (forall pi' sig' A', 
    In ((pi',sig'),A') l -> ((assrt_interp (pi',sig')) ==> (L_assrt_interp A'))    
  ) ->
  ((assrt_interp (pi,sig)) ==> (L_assrt_interp A)).
  intros.
  destruct A.
  (* L_elt *)
  destruct a.
  simpl in H.
  assert (frag_decision (pi, sig) (p, s) = true \/ frag_decision (pi, sig) (p, s) = false).
  destruct (frag_decision (pi, sig) (p, s)); intuition.
  inversion_clear H1.
  red; intros.
  generalize (frag_decision_correct _ _ H2 _ _ H1); intros.
  auto.
  rewrite H2 in H.
  discriminate.
  (* L_subst *)
  destruct A.
  (****************************************************************)
  (* L_elt *)  
  simpl in H.
  red; injection H; intros; subst l; clear H.
  simpl in H0.
  assert ((pi, sig, L_elt (subst_assrt_lst l0 a)) = (pi, sig, L_elt (subst_assrt_lst l0 a)) \/ False).
  left; auto.
  generalize (H0 _ _ _ H s h); clear H H0; intros.
  generalize (H H2); clear H; intros.
  simpl in H.
  simpl.
  destruct a.
  eapply subst_lst2update_store_assrt_interp.
  auto.
  (* L_subst *)  
  simpl in H.
  red; injection H; intros; subst l; clear H.
  simpl in H0.
  assert ((pi, sig, L_subst (l1 ++ l0) A) = (pi, sig, L_subst (l1 ++ l0) A) \/ False).
  left; auto.
  generalize (H0 _ _ _ H s h); clear H H0; intros.
  generalize (H H2); clear H; intros.
  simpl in H.
  simpl.
  eapply subst_lst2update_store_app.
  auto.
  (* L_lookup *)
  simpl in H.
  red; intros.
  simpl.
  assert (Sigma_get_cell_val (subst_e_lst l0 e) sig pi = None \/ exists v, Sigma_get_cell_val (subst_e_lst l0 e) sig pi = Some v).
  destruct (Sigma_get_cell_val (subst_e_lst l0 e) sig pi).
  right; exists e0; auto.
  left; auto.
  inversion_clear H2.
  rewrite H3 in H.
  discriminate.
  inversion_clear H3.
  rewrite H2 in H.
  injection H; clear H; intros; subst l.
  simpl in H0.
  assert ((pi, sig,
       L_subst
         ((v, var_e (max (max (var_max_lst l0) (var_max_L_assrt A)) v + 1))
          :: l0 ++
             (max (max (var_max_lst l0) (var_max_L_assrt A)) v + 1, x) :: nil)
         A) = (pi, sig,
       L_subst
         ((v, var_e (max (max (var_max_lst l0) (var_max_L_assrt A)) v + 1))
          :: l0 ++
             (max (max (var_max_lst l0) (var_max_L_assrt A)) v + 1, x) :: nil)
         A) \/ False).
  tauto.
  generalize (H0 _ _ _ H s h); clear H H0; intros.
  generalize (H H1); clear H; intros.
  simpl in H.
  simpl in H1.
  generalize (Sigma_get_cell_val_correct _ _ _ _ H2 _ _ (proj1 H1) (proj2 H1)); intros.
  
  apply (subst_lst2update_store_exists l0 
  (fun e0 s h => (e |-> e0 ** (e |-> e0 -* update_store2 v e0 (L_assrt_interp A))) s h) 
  s h).
  exists (int_e (eval x s)).  
  apply (subst_lst2update_store_sep_con l0 (e |-> int_e (eval x s)) (e |-> int_e (eval x s) -* update_store2 v (int_e (eval x s)) (L_assrt_interp A))).
  simpl in H0.
  Decompose_sepcon H0 h1 h2.
  Compose_sepcon h1 h2.
  apply subst_lst2update_store_mapsto.
  Mapsto.
  rewrite subst_e_lst_int_e; auto.
  apply subst_lst2update_store_sepimp.
  red; intros.
  inversion_clear H5.
  generalize (subst_lst2update_store_mapsto' _ _ _ _ _ H9); clear H9; intros.
  assert (h' = h1).
  eapply singleton_equal.
  apply H5.
  apply H3.
  auto.
  rewrite subst_e_lst_int_e; auto.
  subst h'.
  assert (h'' = h).
  Equal_heap.
  rewrite H9.
  unfold update_store2.
  simpl.
  generalize (subst_lst2update_store' _ _ _ _ _ _ H); intro.
  unfold update_store2 in H10.
  eapply intro_fresh_var with (max (max (var_max_lst l0) (var_max_L_assrt A)) v + 1); auto.
  red.
  assert (max (max (var_max_lst l0) (var_max_L_assrt A)) v >= var_max_lst l0).
  apply max_lemma5.
  apply max_lemma4.
  omega.
  red.
  assert (max (max (var_max_lst l0) (var_max_L_assrt A)) v >= var_max_L_assrt A).
  apply max_lemma5.
  apply max_lemma6.
  omega.
  omega.
  red.
  simpl.
  assert (max (max (var_max_lst l0) (var_max_L_assrt A)) v >= v).
  apply max_lemma6.
  omega.
  omega.
  (* L_mutation *)
  simpl in H.
  red; intros.
  simpl.
  injection H; clear H; intros; subst l.
  simpl in H0.
  assert ((pi, sig, L_mutation (subst_e_lst l0 e) (subst_e_lst l0 e0) (L_subst l0 A)) = (pi, sig, L_mutation (subst_e_lst l0 e) (subst_e_lst l0 e0) (L_subst l0 A)) \/ False).
  tauto.
  generalize (H0 _ _ _ H s h); clear H H0; intros.
  generalize (H H1); clear H; intros.
  simpl in H.
  inversion_clear H.
  Decompose_sepcon H0 h1 h2.
  apply (subst_lst2update_store_exists l0 
  (fun e1 s h => (e |-> e1 ** (e |-> e0 -* L_assrt_interp A)) s h)).
  exists (int_e (eval x s)).  
  apply (subst_lst2update_store_sep_con l0 (e |-> int_e (eval x s)) (e |-> e0 -* L_assrt_interp A)).
  Compose_sepcon h1 h2.
  apply subst_lst2update_store_mapsto.
  Mapsto.
  rewrite subst_e_lst_int_e; auto.
  apply subst_lst2update_store_sepimp.
  red; intros.
  eapply H4.
  inversion_clear H3.
  split.
  apply H6.
  generalize (subst_lst2update_store_mapsto' _ _ _ _ _ H7); clear H7; intros.
  auto.
  auto.
  (* L_if *)
  simpl in H.
  red; injection H; intros; subst l; clear H.
  simpl in H0.
  assert ((pi, sig,L_if (subst_b_lst l0 e) (L_subst l0 A1) (L_subst l0 A2)) = (pi, sig,L_if (subst_b_lst l0 e) (L_subst l0 A1) (L_subst l0 A2)) \/ False).
  left; auto.
  generalize (H0 _ _ _ H s h); clear H H0; intros.
  generalize (H H2); clear H; intros.
  simpl in H.  
  simpl.
  apply (subst_lst2update_store_and' l0 
    (fun s0 h0 => s0 |b= e -> L_assrt_interp A1 s0 h0) 
    (fun s0 h0 => s0 |b!= e -> L_assrt_interp A2 s0 h0)).
  simpl in H.
  inversion_clear H.
  split.
  eapply (subst_lst2update_store_imply l0 (fun s0 h0 => s0 |b= e) (fun s0 h0 => L_assrt_interp A1 s0 h0)).
  intros.
  generalize (H0 (subst_lst2update_store_subst_b_lst _ _ _ _ _ H)); intros.
  eapply entails_subst_lst2update_store; [idtac | apply H3].
  red; intros; auto.
  eapply (subst_lst2update_store_imply l0 (fun s0 h0 => s0 |b!= e) (fun s0 h0 => L_assrt_interp A2 s0 h0)).
  intros.
  generalize (H1 (subst_lst2update_store_subst_b_lst _ _ _ _ _ H)); intros.
  eapply entails_subst_lst2update_store; [idtac | apply H3].
  red; intros; auto.
  (****************************************************************)
  (* L_lookup *)
  red; intros.
  simpl in H.
  simpl in H1; simpl.
  assert (Sigma_get_cell_val e sig pi = None \/ exists v, Sigma_get_cell_val e sig pi = Some v).
  destruct (Sigma_get_cell_val e sig pi).
  right; exists e0; auto.
  left; auto.
  inversion_clear H2.
  rewrite H3 in H; discriminate.
  inversion_clear H3.
  rewrite H2 in H.
  injection H; intros; subst l; clear H.
  assert ((pi, sig, L_subst ((v, x) :: nil) A) = (pi, sig, L_subst ((v, x) :: nil) A) \/ False).
  tauto.
  generalize (H0 _ _ _ H _ _ H1); clear H H0; intros.
  generalize (Sigma_get_cell_val_correct _ _ _ _ H2 _ _ (proj1 H1) (proj2 H1)); intros.
  simpl in H0.
  exists x.
  apply cell_read.
  split; auto.
  (* L_mutation *)
  red; intros.
  simpl in H.
  assert (Sigma_elt_term_extract' (cell e) sig pi = None \/ exists v, Sigma_elt_term_extract' (cell e) sig pi = Some v).
  destruct (Sigma_elt_term_extract' (cell e) sig pi).
  right; exists s0; auto.
  left; auto.
  inversion_clear H2.
  rewrite H3 in H; discriminate.
  inversion_clear H3.
  rewrite H2 in H.
  injection H; intros; subst l; clear H.
  simpl in H0.
  assert ((pi, star (singl e e0) x, A) = (pi, star (singl e e0) x, A) \/ False).
  tauto.
  simpl in H1.
  generalize (H0 _ _ _ H); clear H H0; intros.
  simpl.  
  generalize (Sigma_elt_term_extract'_correct _ _ _ _ H2 _ _ (proj1 H1) (proj2 H1)); intros.
  simpl in H0.
  Decompose_sepcon H0 h1 h2.
  inversion_clear H3.
  exists (int_e x0).
  Compose_sepcon h1 h2.
  auto.
  red; intros.  
  apply H.
  split; try tauto.
  simpl.
  inversion_clear H3.
  Compose_sepcon h' h2.
  auto.
  auto.
  (* L_if *)
  red; intros.
  simpl in H.
  injection H; intros; subst l; clear H.
  simpl in H0.
  simpl.
  split.
  intros.
  unfold sep.entails in H0.
  eapply H0.
  left; intuition.
  simpl in H1.
  inversion_clear H1.
  split.
  Omega_exprb.
  auto.
  intros.
  unfold sep.entails in H0.
  eapply H0.
  right; left; intuition.
  simpl in H1.
  inversion_clear H1.
  split.
  Omega_exprb.
  auto.
Qed.
    
Transparent frag_decision.


Lemma LWP_list_correct: forall l l',
  LWP_list l = Some l' ->
  (forall pi sig A, In ((pi,sig),A) l' ->
    ((assrt_interp (pi,sig)) ==> (L_assrt_interp A))) ->
  (forall pi sig A, In ((pi,sig),A) l -> ((assrt_interp (pi,sig)) ==> (L_assrt_interp A))).
  unfold sep.entails.
  induction l.
  simpl; intros.
  contradiction.
  destruct a.
  destruct p.
  simpl; intros.
  assert (LWP_step p s l0 = None \/ exists v, LWP_step p s l0 = Some v).
  destruct (LWP_step p s l0).
  right; exists l1; auto.
  left; auto.
  inversion_clear H3.
  rewrite H4 in H.
  discriminate.
  inversion_clear H4.
  rewrite H3 in H.
  assert (LWP_list l = None \/ exists v, LWP_list l = Some v).
  destruct (LWP_list l).
  right; exists l1; auto.
  left; auto.
  inversion_clear H4.
  rewrite H5 in H; discriminate.
  inversion_clear H5.
  rewrite H4 in H.
  injection H; clear H; intros; subst l'.
  
  inversion_clear H1.
  injection H; clear H; intros; subst p s A.
  generalize LWP_step_correct; intro X.
  unfold sep.entails in X.
  eapply X.
  apply H3.
  intros.
  eapply H0.
  apply in_or_app.
  left; apply H.
  auto.
  auto.
   
  eapply IHl.
  apply H4.
  simpl.
  intros.
  eapply H0.
  apply in_or_app.
  right.
  apply H1.
  auto.
  apply H.
  auto.
Qed.

Lemma LWP_list_rec_correct: forall a l l',
  LWP_list_rec l a = Some l' ->
  (forall pi sig A, In ((pi,sig),A) l' ->
    ((assrt_interp (pi,sig)) ==> (L_assrt_interp A))) ->
  (forall pi sig A, In ((pi,sig),A) l -> ((assrt_interp (pi,sig)) ==> (L_assrt_interp A))).
  unfold sep.entails.
  induction a.
  simpl.
  intros.
  eapply H0.
  injection H; intros; subst l'.
  apply H1.
  auto.
  
  simpl ; intros.
  
  assert (LWP_list l = None \/ exists v, LWP_list l = Some v).
  destruct (LWP_list l).
  right; exists l0; auto.
  left; auto.
  
  inversion_clear H3.
  rewrite H4 in H.
  discriminate.
  inversion_clear H4.
  rewrite H3 in H.
  generalize LWP_list_correct; intro X.
  unfold sep.entails in X.
  eapply X.
  apply H3.
  intros.
  eapply IHa.
  apply H.
  intros.
  eapply H0.
  apply H6.
  auto.
  apply H4.
  auto.
  apply H1.
  auto.
Qed.

Lemma frag_hoare_correct: forall P Q c,
  frag_hoare P Q c = true ->
  {{assrt_interp P}}
  c
  {{assrt_interp Q}}.
  intros.
  unfold frag_hoare in H.
  assert (wp_frag (Some (L_elt Q)) c = None \/ exists L, wp_frag (Some (L_elt Q)) c = Some L).
  destruct (wp_frag (Some (L_elt Q)) c).
  right; exists l; auto.
  left; auto.
  inversion_clear H0.
  rewrite H1 in H;discriminate.
  inversion_clear H1.
  cutrewrite (assrt_interp Q = L_assrt_interp (L_elt Q)); auto.
  eapply semax_strengthen_pre; [idtac | eapply wp_frag_soudness; apply H0]; auto.
  rewrite H0 in H.
  destruct P.
  assert (LWP_list_rec ((p, s, x) :: nil) (L_assrt_size x) = None \/ exists v, LWP_list_rec ((p, s, x) :: nil) (L_assrt_size x) = Some v).
  destruct (LWP_list_rec ((p, s, x) :: nil) (L_assrt_size x)).
  right; exists l; auto.
  left; auto.
  inversion_clear H1.
  rewrite H2 in H; discriminate.
  inversion_clear H2.
  rewrite H1 in H.
  destruct x0; try discriminate.
  intros.
  eapply LWP_list_rec_correct.
  apply H1.
  intros.
  simpl in H2; contradiction.
  intuition.
Qed.

(*Recursive Extraction frag_hoare.*)

  

  

  
  
  
  
  
  





