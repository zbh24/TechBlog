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

Require Import frag2.

Import Fresh.

Require Import expr_b_dp.

Inductive forward : assrt -> assrt -> cmd -> assrt -> Prop :=

  | forward_str_precond: forall P P' Q Q' c,
    (assrt_interp P ==> assrt_interp P') ->
    forward Q P' c Q' ->
    forward Q P c Q'

  | forward_skip: forall P Q,
    forward Q P skip P

  | forward_assign: forall pi sig x e x' Q,
    fresh_assrt x' (pi, sig) ->
    fresh_e x' e ->
    fresh_e x' (var_e x) ->
    fresh_assrt x' Q ->
    forward Q (pi, sig) (x <- e) (((expr_b_rewrite pi (var_e x) (var_e x')) &&& ((var_e x) == (expr_rewrite e (var_e x) (var_e x')))), subst_Sigma sig x (var_e x'))

  | forward_lookup: forall pi sig e1 e2 e x x' Q, 
    (forall s, eval_b pi s = true -> eval_b (e1 == e) s = true) ->
    fresh_assrt x' (pi, star sig (singl e1 e2)) ->
    fresh_e x' e ->
    fresh_e x' (var_e x) ->
    fresh_assrt x' Q ->
    forward Q (pi,star sig (singl e1 e2)) (x <-* e) (((expr_b_rewrite pi (var_e x) (var_e x')) &&& ((var_e x) == (expr_rewrite e2 (var_e x) (var_e x')))), subst_Sigma (star sig (singl e1 e2)) x (var_e x'))

  | forward_mutation: forall pi1 sig1 e1 e2 e3 e4 Q, 
    (forall s, eval_b pi1 s = true -> eval_b (e1 == e3) s = true) ->
    forward Q (pi1,star sig1 (singl e1 e2)) (e3 *<- e4) (pi1,star sig1 (singl e1 e4))
    
  | forward_mutation': forall pi1 sig1 e1 e3 e4 Q, 
    (forall s, eval_b pi1 s = true -> eval_b (e1 == e3) s = true) ->    
    forward Q (pi1,star sig1 (cell e1)) (e3 *<- e4) (pi1,star sig1 (singl e1 e4))

  | forward_unroll_lst: forall pi sig e1 e2 c x' Q Q', 
    fresh_assrt x' (pi, star sig (lst e1 e2)) ->
    fresh_cmd x' c ->
    (forall s, s |b= (pi =b> (e1 =/= e2))) ->
    forward Q (pi &&& (e1 == (var_e x')),star sig (star (star (singl e1 (var_e x')) (cell (e1 +e (nat_e 1)))) (lst (var_e x') e2))) c Q' ->
    forward Q (pi,star sig (lst e1 e2)) c Q'.

Lemma forward_sound: forall P c Q Q',
  forward Q P c Q' ->
  ((assrt_interp Q') ==> (assrt_interp Q)) ->
  {{assrt_interp P}} c {{assrt_interp Q}}.

  do 5 intro.
  induction H; intros.

  (* precond str. *)
  eapply semax_strengthen_pre with (assrt_interp P'); auto.

  (* skip *)

  eapply semax_strengthen_pre with (assrt_interp Q); auto.
  eapply semax_skip.

  (* x <- e *)

  eapply semax_complete.
  red; intros.
  split; intros.
  red; intro X; inversion_clear X.
  inversion_clear H4.
  inversion H5.
  subst s'; subst h'; clear H11 H10 H9 H8 e0 x0 h0 s0 H5.
  assert (In x' (x'::nil)).
  simpl; left; auto.
  eapply (proj2 (fresh_assrt_inde _ _ H2 (store.update x (eval e s) s) h x' (eval (var_e x) s) H4)).
  clear H4.
  simpl eval.
  red in H3; eapply H3.
  split.
  cut (
    (store.update x' (store.lookup x s) (store.update x (eval e s) s)
      |b= expr_b_rewrite pi (var_e x) (var_e x')) /\
    (store.update x' (store.lookup x s) (store.update x (eval e s) s)
      |b= (var_e x == expr_rewrite e (var_e x) (var_e x')))
  ).
  intro X; inversion_clear X; Omega_exprb.
  split.
  rewrite <- eval_b_store_update.
  simpl eval.
  rewrite (store.lookup_update').
  rewrite store.update_update.
  rewrite store.update_update'.
  rewrite store.update_lookup.
  assert (In x' (x'::nil)).
  simpl; left; auto.  
  assert (fresh_b x' pi).
  Max_inf_resolve.
  eapply (proj1 (fresh_b_inde pi x' true H5 s h x' (store.lookup x s) H4)).
  auto.
  Max_inf_resolve.
  simpl.
  rewrite <- eval_store_update.
  simpl.
  rewrite store.lookup_update'.
  rewrite <- store.lookup_update.
  rewrite store.lookup_update'.
  rewrite store.update_update.
  rewrite store.update_update'.
  rewrite store.update_lookup.  
  rewrite (fresh_e_eval e x' (store.lookup x s) s H0).
  eapply Zeq_bool_refl.
  Max_inf_resolve.
  Max_inf_resolve.
  eapply subst_Sigma2store_update'.
  simpl.
  rewrite store.lookup_update'.
  rewrite store.update_update.
  rewrite store.update_lookup_update.
  assert (fresh_Sigma x' sig).
  Max_inf_resolve.
  assert (In x' (x'::nil)).
  simpl; left; auto.  
  eapply (proj1 (var_max_Sigma_inde sig x' H4 s h x' (store.lookup x s) H5)); auto.
  Max_inf_resolve.

  (* x<-* e *)
  
  eapply semax_complete.
  red; intros.
  split; intros.
  red; intro X; inversion_clear X.
  simpl in H5.
  inversion_clear H5.
  Decompose_sepcon H9 h1 h2.
  inversion_clear H12.
  inversion_clear H11.
  assert (x0 = p).
  rewrite <- H6; rewrite <- H12.
  cutrewrite (eval e1 s = eval e s); auto.
  generalize (H _ H8); intros; Omega_exprb.
  rewrite H11 in H13.
  assert (heap.lookup p h = Some (eval e2 s)).
  rewrite H10.
  eapply heap.lookup_union_R.
  auto.
  rewrite H13.
  rewrite heap.lookup_singleton; auto.
  rewrite H7 in H14; discriminate.
  
  inversion_clear H5.
  inversion H6.
  subst s'; subst h'; clear H12 H10 H9 H5 e0 x0 h0 s0 H6.
  assert (In x' (x'::nil)).
  simpl; left; auto.
  eapply (proj2 (fresh_assrt_inde _ _ H3 (store.update x v s) h x' (eval (var_e x) s) H5)).
  clear H5.
  simpl eval.
  red in H4; eapply H4.
  split.
  cut (
    (store.update x' (store.lookup x s) (store.update x v s)
    |b= expr_b_rewrite pi (var_e x) (var_e x')) /\
    (store.update x' (store.lookup x s) (store.update x v s)
      |b= (var_e x == expr_rewrite e2 (var_e x) (var_e x')))
  ).
  intro X; inversion_clear X; Omega_exprb.
  split.
  rewrite <- eval_b_store_update.
  simpl eval.
  rewrite store.lookup_update'.
  rewrite store.update_update.
  rewrite store.update_update'.
  rewrite store.update_lookup.
  assert (In x' (x'::nil)).
  simpl; left; auto.  
  assert (fresh_b x' pi).
  Max_inf_resolve.
  eapply (proj1 (fresh_b_inde pi x' true H6 s h x' (store.lookup x s) H5)).
  auto.
  Max_inf_resolve.
  simpl.
  rewrite <- eval_store_update.
  simpl.
  rewrite store.lookup_update'.
  rewrite <- store.lookup_update.
  rewrite store.lookup_update'.
  rewrite store.update_update.
  rewrite store.update_update'.
  rewrite store.update_lookup.  
  assert (v = eval e2 s).
  simpl in H8.
  Decompose_sepcon H8 h1 h2.
  inversion_clear H10.
  inversion_clear H9.
  assert (x0 = p).
  rewrite <- H10; rewrite <- H11.
  cutrewrite (eval e1 s = eval e s); auto.
  generalize (H _ H7); intros; Omega_exprb.
  rewrite H9 in H12.
  assert (heap.lookup p h = Some (eval e2 s)).
  rewrite H8.
  eapply heap.lookup_union_R.
  auto.
  rewrite H12.
  rewrite heap.lookup_singleton; auto.
  rewrite H13 in H15; injection H15; auto.
  subst v.
  rewrite (fresh_e_eval e2 x' (store.lookup x s) s).
  eapply Zeq_bool_refl.
  Max_inf_resolve.
  Max_inf_resolve.
  Max_inf_resolve.
  eapply subst_Sigma2store_update'.
  simpl.
  rewrite store.lookup_update'.
  rewrite store.update_update.
  rewrite store.update_lookup_update.
  simpl in H8.
  Decompose_sepcon H8 h1 h2.
  Compose_sepcon h1 h2.
  assert (fresh_Sigma x' sig).
  Max_inf_resolve.
  assert (In x' (x'::nil)).
  simpl; left; auto.  
  eapply (proj1 (var_max_Sigma_inde sig x' H9 s h1 x' (store.lookup x s) H12)); auto.
  Mapsto.
  rewrite (fresh_e_eval e1 x' (store.lookup x s) s); auto.
  Max_inf_resolve.
  rewrite (fresh_e_eval e2 x' (store.lookup x s) s); auto.  
  Max_inf_resolve.
  Max_inf_resolve.

  (* e3 *<- e4 *)

  eapply semax_mutation_backwards'.
  simpl; red; intros.
  inversion_clear H1.
  Decompose_sepcon H3 h1 h2.
  exists e2.
  Compose_sepcon h2 h1.
  Mapsto.
  generalize (H _ H2); intros; Omega_exprb.
  Intro_sepimp h2' h''.
  red in H0; eapply H0.
  simpl.
  split; auto.
  Compose_sepcon h1 h2'; auto.
  Mapsto.
  generalize (H _ H2); intros; Omega_exprb.

  (* e3 *<- e4 *)
  
  eapply semax_mutation_backwards'.
  simpl; red; intros.
  inversion_clear H1.
  Decompose_sepcon H3 h1 h2.
  inversion_clear H6.
  exists (int_e x).
  Compose_sepcon h2 h1.
  Mapsto.
  generalize (H _ H2); intros; Omega_exprb.
  Intro_sepimp h2' h''.
  red in H0; eapply H0.
  simpl.
  split; auto.
  Compose_sepcon h1 h2'; auto.
  Mapsto.
  generalize (H _ H2); intros; Omega_exprb.

  (* unroll lst *)
Admitted.

Require Import Max.

(* a finir *)

Definition forward_fct (Q: assrt) (pi: expr_b) (sig: Sigma) (c:cmd) : option assrt :=
  match c with
    | x <- e =>
      let x' := ((max (var_max_assrt Q) (max (var_max_assrt (pi,sig)) (max x (var_max_expr e)))) +1)  in (
        Some (((expr_b_rewrite pi (var_e x) (var_e x')) &&& ((var_e x) == (expr_rewrite e (var_e x) (var_e x')))), subst_Sigma sig x (var_e x'))        
      )
    | x <-* e => 
      match sig with
        | (singl e1 e2) =>
          if (expr_b_dp (pi =b> (e1 == e))) then
            let x' := ((max (var_max_assrt Q) (max (var_max_assrt (pi,sig)) (max x (var_max_expr e)))) +1)  in (
              Some (((expr_b_rewrite pi (var_e x) (var_e x')) &&& ((var_e x) == (expr_rewrite e (var_e x) (var_e x')))), subst_Sigma sig x (var_e x'))
            ) else None
        | star sig' (singl e1 e2) =>
          if (expr_b_dp (pi =b> (e1 == e))) then
            let x' := ((max (var_max_assrt Q) (max (var_max_assrt (pi,sig)) (max x (var_max_expr e)))) +1)  in (
              Some (((expr_b_rewrite pi (var_e x) (var_e x')) &&& ((var_e x) == (expr_rewrite e (var_e x) (var_e x')))), subst_Sigma sig x (var_e x'))
            ) else Some (pi,(Sigma_clean_epsi (Sigma_assoc_left (Sigma_com sig) epsi) pi))
        | _ => Some (pi,(Sigma_clean_epsi (Sigma_assoc_left (Sigma_com sig) epsi) pi))
      end
    | _ => None
  end.
  
  
  
  
  
  
  
  
  
