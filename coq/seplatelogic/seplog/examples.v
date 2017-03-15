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

Open Local Scope Z_scope.

(****************************************************************************)
(*                              GCD                                         *)
(****************************************************************************)

Module GCD.

Require Import Znumtheory.

(* original version by Euclid *)
Definition gcd0 a b x y :=
  x <- int_e a;
  y <- int_e b;
  while (var_e x =/= var_e y) (
    ifte (var_e y >> var_e x) thendo
    (y <- var_e y -e var_e x)
    elsedo
    (x <- var_e x -e var_e y)
  ).

Definition x := 0%nat.
Definition y := 1%nat.

Lemma gcd0_verif : forall a b,
  {{ fun s h => 0 < a /\ 0 < b }}
  gcd0 a b x y
  {{ fun s h => exists d, store.lookup x s = d /\ Zis_gcd a b d }}.
  intros.
  unfold gcd0.
  (********************  x <- int_e a; ********************)
  apply semax_assign'' with (fun s (_:heap.h) => 0 < a /\ 0 < b /\ store.lookup x s = a).
  red; intros; red.
  rewrite store.lookup_update'.
  tauto.
  (********************  x <- int_e b; ********************)
  apply semax_assign'' with (fun s (_:heap.h) => 0 < a /\ 0 < b /\ store.lookup x s = a /\ store.lookup y s = b).
  red; intros; red.
  elim store.lookup_update.
  rewrite store.lookup_update'.
  tauto.
  unfold x; unfold y; omega.
 (******************** while (var_e x =/= var_e y) ********************)
  apply semax_strengthen_pre with (fun s (_:heap.h) => 
    exists vx, exists vy, exists d, 0 < vx /\ 0 < vy /\ 
      store.lookup x s = vx /\ store.lookup y s = vy /\ 
      Zis_gcd vx vy d /\ Zis_gcd a b d).
  red; intros.
  exists a; exists b.
  generalize (Zgcd_spec a b); intro X; inversion_clear X as [d].
  exists d; tauto.
  apply semax_weaken_post with (fun s (_:heap.h) => 
    (exists vx, exists vy, exists d, 0 < vx /\ 0 < vy /\ 
      store.lookup x s = vx /\ store.lookup y s = vy /\
      Zis_gcd vx vy d /\ Zis_gcd a b d)
    /\ eval_b (var_e x =/= var_e y) s = false
  ).
  red; intros.
  inversion_clear H.
  inversion_clear H0 as [vx].
  inversion_clear H as [vy].
  simpl in H1.
  generalize (negb_false_is_true _ H1); clear H1; intro.
  generalize (Zeq_bool_true _ _ H); clear H; intro.
  inversion_clear H0 as [d].
  decompose [and] H1; clear H1.
  rewrite H in H2; rewrite H2 in H4; subst vy.
  assert (0 <= vx).
  omega.
  generalize (Zis_gcd_eq _ _ H1 H5); intro.
  inversion_clear H4.
  exists d.
  split; auto.
  rewrite H; rewrite H2; auto.
  exists (-d).
  split.
  rewrite H; rewrite H2; auto.
  apply Zis_gcd_opp.
  apply Zis_gcd_sym.
  auto.
  apply semax_while with (P:=fun s (_:heap.h) => 
    (exists vx, exists vy, exists d, 0 < vx /\ 0 < vy /\ 
      store.lookup x s = vx /\ store.lookup y s = vy /\
      Zis_gcd vx vy d /\ Zis_gcd a b d)).
 (******************** ifte var_e y >> var_e x ********************)
  apply semax_ifte.
  (******************** y <- var_e y -e var_e x ********************)
  apply semax_assign'.
  red; intros.
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H as [vx].
  inversion_clear H0 as [vy].
  inversion_clear H as [d].
  decompose [and] H0; clear H0.
  red.
  exists vx; exists (vy-vx); exists d.
  elim store.lookup_update.
  rewrite store.lookup_update'.
  split; trivial.
  split.
  simpl in H2.
  assert (vy > vx).
  apply Zgt_bool_true.
  rewrite <-H3; rewrite <-H5; assumption.
  omega.
  split; trivial.
  split.
  simpl.
  rewrite <-H3; rewrite <-H5; reflexivity.
  split; trivial.
  cutrewrite (vy-vx = vx * (-1) + vy); [idtac | ring].
  apply Zis_gcd_for_euclid2.
  apply Zis_gcd_sym.
  assumption.
  unfold x; unfold y; omega.
  (********************* }x <- var_e x -e var_e y ********************)
  apply semax_assign'.
  red; intros.
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H as [vx].
  inversion_clear H0 as [vy].
  inversion_clear H as [d].
  decompose [and] H0; clear H0.
  red.
  exists (vx-vy); exists vy; exists d.
  rewrite store.lookup_update'.
  elim store.lookup_update.
  split.
  assert (vy < vx).
  apply Zle_neq_lt.
  simpl in H2; simpl in H3.
  apply Zgt_bool_false.
  rewrite <-H3; rewrite <-H5; assumption.
  apply Zeq_bool_false'.
  apply negb_true_is_false.
  rewrite Zeq_bool_sym.
  rewrite <-H3; rewrite <-H5; assumption.
  omega.
  split; trivial.
  split.
  simpl.
  rewrite <-H3; rewrite <-H5; reflexivity.
  split; trivial.
  split; trivial.
  apply Zis_gcd_sym.
  cutrewrite (vx - vy = vy * (-1) + vx); [idtac | ring].
  apply Zis_gcd_for_euclid2.
  assumption.
  unfold x; unfold y; omega.
Qed.

Definition a := 0%nat.
Definition b := 1%nat.
Definition r := 2%nat.

(* classical algorithm *)
Definition gcd1 a b r :=
  while (var_e b =/= int_e 0) (
    r <- (var_e a) mode (var_e b);
    a <- var_e b;
    b <- var_e r
  ).

Lemma gcd1_verif : forall va vb, 0 <= va -> 0 <= vb ->
  {{ fun s h => store.lookup a s = va /\ store.lookup b s = vb }}
  gcd1 a b r
  {{ fun s h => exists wa, exists wb, exists d,
    store.lookup a s = wa /\ store.lookup b s = wb /\
    Zis_gcd wa wb d /\ Zis_gcd va vb d }}.
  intros.
  unfold gcd1.
  (********************* while (var_e b =/= int_e 0) ********************)
  apply semax_strengthen_pre with (fun s (h:heap.h) =>
    exists wa, (exists wb, (exists d,
      0 <= wa /\ 0 <= wb /\
      store.lookup a s = wa /\ store.lookup b s = wb /\ 
      Zis_gcd wa wb d /\ Zis_gcd va vb d))).
  red; intros.
  exists va; exists vb.
  generalize (Zgcd_spec va vb); intro X; inversion_clear X as [d].
  exists d.
  tauto.
  apply semax_weaken_post with (fun s (_ : heap.h) =>
    (exists wa, (exists wb, (exists d,
      0 <= wa /\ 0 <= wb /\
      store.lookup a s = wa /\ store.lookup b s = wb /\ 
      Zis_gcd wa wb d /\ Zis_gcd va vb d)))
    /\
    eval_b (var_e b =/= int_e 0) s = false).
  red; intros.
  inversion_clear H1.
  inversion_clear H2 as [wa].
  inversion_clear H1 as [wb].
  inversion_clear H2 as [d].
  exists wa; exists wb; exists d; tauto.
  apply semax_while with (P:=fun s (_:heap.h) =>
    exists wa, (exists wb, (exists d,
      0 <= wa /\ 0 <= wb /\
      store.lookup a s = wa /\
      store.lookup b s = wb /\ Zis_gcd wa wb d /\ Zis_gcd va vb d))).
  (********************* r <- var_e a mode var_e b; ********************)
  apply semax_assign'' with (fun s (_ : heap.h) =>
    (exists wa, (exists wb, (exists d,
      0 <= wa /\ 0 < wb /\
      store.lookup a s = wa /\ store.lookup b s = wb /\ 
      Zis_gcd wa wb d /\ Zis_gcd va vb d /\ store.lookup r s = Zmod wa wb)))).
  red; intros.
  inversion_clear H1.
  inversion_clear H2 as [wa].
  inversion_clear H1 as [wb].
  inversion_clear H2 as [d].
  red.
  exists wa; exists wb; exists d.
  elim store.lookup_update.
  elim store.lookup_update.
  rewrite store.lookup_update'.
  split; try tauto.
  split.
  simpl in H3.
  generalize (negb_true_is_false _ H3); intro.
  generalize (Zeq_bool_false' _ _ H2); intro.
  decompose [and] H1; clear H1.
  rewrite H8 in H4.
  omega.
  split; try tauto.
  split; try tauto.
  split; try tauto.
  split; try tauto.
  simpl.
  decompose [and] H1; clear H1.
  rewrite <-H6; rewrite <-H4; auto.
  unfold b; unfold r; omega.
  unfold a; unfold r; omega.
  (********************* a <- var_e b; ********************)
  apply semax_assign'' with (fun s (_ : heap.h) =>
    exists wa, (exists wb, (exists d,
      0 <= wa /\ 0 < wb /\
      store.lookup a s = wb /\ store.lookup b s = wb /\
      Zis_gcd wa wb d /\ Zis_gcd va vb d /\ 
      store.lookup r s = wa mod wb))).
  red; intros; red.
  inversion_clear H1 as [wa].
  inversion_clear H2 as [wb].
  inversion_clear H1 as [d].
  exists wa; exists wb; exists d.
  rewrite store.lookup_update'.
  elim store.lookup_update.
  elim store.lookup_update.
  tauto.
  unfold r; unfold a; omega.
  unfold b; unfold a; omega.
  (********************* b <- var_e r ********************)
  apply semax_assign'.
  red; intros; red.
  inversion_clear H1 as [wa].
  inversion_clear H2 as [wb].
  inversion_clear H1 as [d].
  elim store.lookup_update.
  rewrite store.lookup_update'.
  exists wb; exists (wa mod wb); exists d.
  split; try tauto.
  decompose [and] H2; clear H2.
  omega.
  split; try tauto.
  lapply (Z_mod_lt wa wb).
  intros.
  omega.
  decompose [and] H2; clear H2.
  omega.
  split; try tauto.
  split; try tauto.
  split; try tauto.
  lapply (Z_div_mod_eq wa wb); intros.
  assert (wa mod wb = wb * (- (wa / wb)) + wa).
  assert (wa mod wb = wa - wb * (wa / wb)).
  omega.
  rewrite H3.
  ring.
  rewrite H3.
  apply (Zis_gcd_for_euclid2 (wb) d (-(wa/wb)) wa).
  tauto.
  decompose [and] H2; clear H2.
  omega.
  unfold a; unfold b; omega.
Qed.

End GCD.

(****************************************************************************)
(*                              Factorial                                   *)
(****************************************************************************)

Module Factorial.

Definition Zfact (z:Z) : Z :=
  match z with
    Zpos p => Z_of_nat (fact (nat_of_P p))
    | _ => 1
  end.

Lemma Zfact_neg : forall z, z < 0 -> Zfact z = 1.
  destruct z.
  intros.
  inversion H.
  intros.
  inversion H.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma Zfact_zero : Zfact 0 = 1.
  simpl.
  reflexivity.
Qed.

Lemma fact_lemma : forall n, (0 < n)%nat -> (fact n = n * fact (n - 1))%nat.
  destruct n; simpl; intros.
  inversion H.
  rewrite <- minus_n_O.
  omega.
Qed.

Lemma Zfact_pos : forall z, z > 0 -> Zfact z = z * Zfact (z - 1).
  destruct z.
  intros.
  inversion H.
  intros.
  simpl Zfact at 1.
  rewrite fact_lemma.
  rewrite inj_mult.
  rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
  assert ( Z_of_nat (fact (nat_of_P p - 1)) =
     Zfact (Zpos p - 1) ).
  assert (Zpos p = 1 \/ 1 < Zpos p).
  omega.
  inversion_clear H0.
  rewrite H1.
  simpl.
  assert (nat_of_P p = 1)%nat.
  rewrite Zpos_eq_Z_of_nat_o_nat_of_P in H1.
  omega.
  rewrite H0.
  simpl.
  reflexivity.
  simpl.
  destruct p.
  unfold Zfact.
  rewrite nat_of_P_minus_morphism.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  rewrite nat_of_P_minus_morphism.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  rewrite H0.
  reflexivity.
  apply lt_O_nat_of_P.
  intros.
  inversion H.
Qed.

Lemma factorial : forall n, 0 <= n ->
  forall x m, var.set (x::m::nil) ->
    {{ fun s h => store.lookup m s = n /\ store.lookup x s = 1 }}
    while (var_e m =/= int_e 0%Z) (
      x <- var_e x *e var_e m;
      m <- var_e m -e int_e 1
    )
    {{ fun s h => store.lookup x s = Zfact n }}. 
  intros n n_pos x m Hvars.
  apply semax_strengthen_pre with (fun s (_:heap.h) =>
    store.lookup x s * Zfact (store.lookup m s) = Zfact n /\
    store.lookup m s >= 0).
  red; intros.
  inversion_clear H.
  rewrite H0.
  rewrite H1.
  omega.
  apply semax_weaken_post with (fun s (_:heap.h) =>
    (store.lookup x s * Zfact (store.lookup m s) = Zfact n /\ 
      store.lookup m s >= 0) /\ 
    eval_b (var_e m =/= int_e 0) s = false).
  red; intros.
  decompose [and] H; clear H.
  assert (store.lookup m s = 0).
  Omega_exprb.
  rewrite H in H2.
  rewrite Zfact_zero in H2.
  unfold val.
  omega.
  apply semax_while with (P:=fun s (_:heap.h) =>
    store.lookup x s * Zfact (store.lookup m s) = Zfact n /\
    store.lookup m s >= 0).
  apply semax_assign'' with (fun s (_:heap.h) =>
    store.lookup x s * Zfact (store.lookup m s - 1) = Zfact n /\
    store.lookup m s - 1 >= 0
  ).
  red; intros.
  red.
  simpl.
  decompose [and] H; clear H.
  rewrite store.lookup_update'.
  rewrite <- (store.lookup_update m x).
  rewrite <-H2.
  pattern (Zfact (store.lookup m s)).
  rewrite Zfact_pos.
  split.
  ring.
  Omega_exprb.
  Omega_exprb.
  simpl in Hvars; intuition.
  apply semax_assign'.
  red; intros.
  red.
  rewrite <- (store.lookup_update x m).
  rewrite store.lookup_update'.
  auto.
  simpl in Hvars; intuition.
Qed.

Open Local Scope vc_scope.

Lemma vc_factorial : forall n, n >= 0 ->
  forall x m, var.set (x::m::nil) ->
    {{ fun s (_:heap.h) => store.lookup m s = n /\ store.lookup x s = 1 }} proj_cmd 
    (while' ((var_e m) =/= int_e 0)
      (fun s (_:heap.h) => store.lookup x s * Zfact (store.lookup m s) = Zfact n /\ store.lookup m s >= 0)
      (x <- var_e x *e var_e m;
	m <- var_e m -e int_e 1))
    {{ fun s (_:heap.h) => store.lookup x s = Zfact n }}. 
  intros n Hpos x m Hvars.
  apply wp_vc_util.
  intros.
    (* vc *)
  simpl.
  unfold update_store2.
  simpl.
  rewrite store.lookup_update'.
  rewrite <- (store.lookup_update x m).
  rewrite store.lookup_update'.
  rewrite <- (store.lookup_update m x).
  split.
  intros.
  decompose [and] H; clear H.
  rewrite <-H2.
  assert (Zeq_bool (store.lookup m s) 0 = true).
  apply negb_false_is_true; auto.
  rewrite (Zeq_bool_true _ _ H).
  rewrite Zfact_zero.  
  unfold val.
  omega.
  split.
  intros.
  decompose [and] H; clear H.
  rewrite <-H2.
  split.
  pattern (Zfact (store.lookup m s)).
  rewrite Zfact_pos.
  ring.
  assert (store.lookup m s <> 0).
  assert (Zeq_bool (store.lookup m s) 0 = false).
  apply negb_true_is_false; auto.
  generalize (Zeq_bool_false (store.lookup m s) 0); intro X; inversion_clear X; auto.
  generalize H3 H; clear H3 H; unfold val; intros; omega.
  assert (store.lookup m s <> 0).
  assert (Zeq_bool (store.lookup m s) 0 = false).
  apply negb_true_is_false; auto.
  generalize (Zeq_bool_false (store.lookup m s) 0); intro X; inversion_clear X; auto.
  generalize H3 H; clear H3 H; unfold val; intros; omega.
  unfold TT; auto.
  simpl in Hvars; intuition.
  simpl in Hvars; intuition.
  (* wp *)
  intros.
  simpl.
  split.
  inversion_clear H.
  rewrite H0.
  rewrite H1.
  ring.
  inversion_clear H; subst n; auto.
Qed.

Close Local Scope vc_scope.

End Factorial.

(***********************************************************************)
(*                              Swap                                   *)
(***********************************************************************)

Module Swap.

Lemma swap: forall x y z v a b, var.set (x::y::z::v::nil) ->
  {{ (var_e x |-> int_e a) ** (var_e y |-> int_e b) }}
  z <-* var_e x; 
  v <-* var_e y; 
  var_e x *<- var_e v; 
  var_e y *<- var_e z
  {{ (var_e x |-> int_e b) ** (var_e y |-> int_e a) }}.
  intros.
  apply semax_lookup_backwards'' with (fun s h => 
    ((var_e x |-> int_e a) ** (var_e y |-> int_e b)) s h /\
    eval (var_e z) s = a
  ).
  red; intros.
  Decompose_sepcon H0 h1 h2.
  exists (int_e a).
  Compose_sepcon h1 h2.
  auto.
  Intro_sepimp h1' h'.
  red.
  split.
  Compose_sepcon h1' h2.
  Mapsto.
  Mapsto.
  Store_update.
  apply semax_lookup_backwards'' with (fun s h => 
    ((var_e x |-> int_e a) ** (var_e y |-> int_e b)) s h /\
    eval (var_e z) s = a /\ eval (var_e v) s = b 
  ).
  red; intros.
  inversion_clear H0.
  Decompose_sepcon H1 h1 h2.
  simpl in H2.
  exists (int_e b).
  Compose_sepcon h2 h1.
  auto.
  Intro_sepimp h2' h'.
  red.
  split.
  Compose_sepcon h1 h2'.
  Mapsto.
  Mapsto.
  split; [Store_update | Store_update].
  apply semax_mutation_backwards'' with (fun s h => 
    ((var_e x |-> int_e b) ** (var_e y |-> int_e b)) s h /\
    eval (var_e z) s = a /\ eval (var_e v) s = b 
  ).
  red; intros.
  decompose [and] H0; clear H0.
  Decompose_sepcon H1 h1 h2.
  exists (int_e a).
  Compose_sepcon h1 h2.
  auto.
  Intro_sepimp h1' h'.
  split.
  Compose_sepcon h1' h2.
  Mapsto.
  Mapsto.
  auto.
  apply semax_mutation_backwards'.
  red; intros.
  decompose [and] H0; clear H0.
  Decompose_sepcon H1 h1 h2.
  exists (int_e b).
  Compose_sepcon h2 h1.
  auto.
  Intro_sepimp h2' h'.
  Compose_sepcon h1 h2'.
  Mapsto.
  Mapsto.
Qed.

Open Local Scope vc_scope.

Lemma vc_swap: forall x y z v a b, var.set (x::y::z::v::nil) ->
  {{ (var_e x |-> int_e a) ** (var_e y |-> int_e b) }}
  proj_cmd
  (z <-*var_e x; 
   v <-* var_e y;
   var_e x *<- var_e v;
   var_e y *<- var_e z)
  {{ (var_e x |-> int_e b) ** (var_e y |-> int_e a) }}.
  intros.
  apply wp_vc_util.
  (* vc *)
  intros.
  simpl.
  unfold TT.
  intuition.
  (* wp *)
  intros.
  simpl.
  exists (int_e a).
  generalize H0; clear H0.
  apply sep.monotony.
  split.
  auto.
  intros.
  generalize H0; clear H0.
  apply sep.adjunction.
  intros.
  red.
  exists (int_e b).
  simpl.
  assert (((var_e y |-> int_e b) ** (var_e x |-> int_e a)) 
    (store.update z (eval (int_e a) s) s) h0).
  apply inde_update_store.
  apply inde_sep_con.
  apply inde_mapsto.
  simpl.
  apply inter_weak.
  apply inter_nil.
  simpl.
  simpl in H; intuition.
  apply inter_weak.
  apply inter_nil.
  simpl.
  simpl in H; intuition.
  apply inde_mapsto.
  simpl.
  apply inter_weak.
  apply inter_nil.
  simpl.
  simpl in H; intuition.
  apply inter_weak.
  apply inter_nil.
  simpl.
  simpl in H; intuition.
  auto.
  generalize H1; clear H1.
  apply sep.monotony.
  split.
  auto.
  intros.
  generalize H1; clear H1.
  apply sep.adjunction.
  intros.
  red.
  simpl.
  exists (int_e a).
  assert (((var_e x |-> int_e a) ** (var_e y |-> int_e b))  (store.update v b (store.update z a s)) h1).
  apply inde_update_store.
  apply inde_sep_con.
  apply inde_mapsto.
  simpl.
  apply inter_weak.
  apply inter_nil.
  simpl.
  simpl in H; intuition.
  apply inter_weak.
  apply inter_nil.
  simpl.
  simpl in H; intuition.
  apply inde_mapsto.
  simpl.
  apply inter_weak.
  apply inter_nil.
  simpl.
  simpl in H; intuition.
  apply inter_weak.
  apply inter_nil.
  simpl.
  simpl in H; intuition.
  auto.
  generalize H2; clear H2.
  apply sep.monotony.
  split.
  auto.
  intros.
  generalize H2; clear H2.
  apply sep.adjunction.
  intros.
  exists (int_e b).
  generalize H2; clear H2.
  apply sep.monotony.
  split.
  auto.
  intros.
  generalize H2; clear H2.
  apply sep.adjunction.
  intros.
  inversion_clear H2.
  inversion_clear H3.
  decompose [and] H2; clear H2.
  inversion_clear H4.
  inversion_clear H2.
  exists x0.
  inversion_clear H7.
  inversion_clear H2.
  exists x1.
  split; auto.
  split; auto.
  split.
  exists x2.
  split; auto.
  simpl.
  simpl in H6.
  rewrite H6.
  rewrite store.lookup_update'.
  auto.
  simpl in H8.
  red.
  exists x3.
  simpl; simpl in H7.
  split; auto.
  rewrite H8.
  rewrite <- (store.lookup_update z v).
  rewrite store.lookup_update'.
  auto.
  Var_uneq.
Qed.

Close Local Scope vc_scope.

End Swap.

(***********************************************************************)
(*                             String copy                             *)
(***********************************************************************)

Module StringCopy.

(* for (c1=buf, c2=s; ( *c1++ = *c2++ )!=0) *)
Definition StringCopy c1 c2 buf str str_tmp :=
  c1 <- var_e buf;
  c2 <- var_e str;
  str_tmp <-* var_e c2;
  while (var_e str_tmp =/= int_e 0) (
    var_e c1 *<- var_e str_tmp;
    c1 <- var_e c1 +e int_e 1;
    c2 <- var_e c2 +e int_e 1;
    str_tmp <-* var_e c2
    );
  var_e c1 *<- var_e str_tmp.

(* generic lemmas about lists *)
  
Lemma fold_right_app_map_nil : forall (A:Set) (lst:list A) (B:Set),
  fold_right (@app B) nil (map (fun _ => nil) lst) = nil.
  induction lst; intros.
  auto.
  simpl.
  apply IHlst.
Qed.

Lemma in_map' : forall (A:Set) (lst:list A) (B:Set) x (f:A->B),
  In x (map f lst) -> exists x', In x' lst /\ x = f x'.
  induction lst; intros.
  simpl in H.
  contradiction.
  simpl in H.
  inversion_clear H.
  exists a.
  split; auto.
  apply in_eq.
  generalize (IHlst _ _ _ H0); intro.
  inversion_clear H.
  exists x0.
  split.
  apply in_cons.
  tauto.
  tauto.
Qed.

Lemma map_length : forall (A:Set) (lst:list A) (B:Set) (f:A->B),
  length (map f lst) = length lst.
  induction lst; intros; auto.
  simpl.
  rewrite IHlst; auto.
Qed.

Lemma del_heads_destruct: forall (A: Set) (l: list A) i a,
  (length l > i)%nat ->
  del_heads l i = nth i l a :: del_heads l (i+1)%nat.
  induction l; simpl; intros.
  inversion H.
  destruct i.
  simpl.
  reflexivity.
  simpl.
  apply IHl.
  omega.
Qed.
Implicit Arguments del_heads_destruct [A].
  
Lemma heads_destruct: forall (A: Set) (l: list A) i a,
  (length l > i)%nat ->
  heads l (i+1) = heads l i ++ (nth i l a)::nil.
  induction l; simpl; intros.
  inversion H.
  destruct i.
  simpl.
  reflexivity.
  simpl.
  rewrite (IHl i a0).
  reflexivity.
  omega.
Qed.
Implicit Arguments heads_destruct [A].

Lemma nth_last: forall (A:Set) (l: list A) n a,
  n = length l ->
  nth n l a = a.
  induction l; simpl; intros.
  rewrite H.
  reflexivity.
  rewrite H.
  apply IHl.
  reflexivity.
Qed.

Lemma heads_last : forall l i,
  l <> nil ->
  i = (length l - 1)%nat ->
  l = heads l i ++ (nth i l (-1))::nil.
  induction l.
  tauto.
  simpl.
  destruct i.
  simpl.
  destruct l; intros; try discriminate.
  reflexivity.
  intros.
  simpl.
  rewrite <-IHl.
  reflexivity.
  destruct l; try discriminate.
  omega.
Qed.

(* relations with expressions *)

Lemma map_expr_var_list_Z : forall (lst:list expr),
  (forall e, In e lst -> expr_var e = nil) ->
  map expr_var lst = map (fun _ => nil) lst.
  induction lst; intros.
  auto.
  simpl.
  rewrite H.
  rewrite IHlst.
  reflexivity.
  intros.
  apply H.
  simpl; auto.
  simpl; auto.
Qed.

Lemma mapstos_equiv : forall l s h e1 e3,
  (e1 |--> l) s h ->
  eval e1 s = eval e3 s ->
  (e3 |--> l) s h.
  induction l.
  simpl; intros.
  auto.
  simpl; intros.
  Decompose_sepcon H h1 h2; Compose_sepcon h1 h2.
  Mapsto.
  eapply IHl.
  apply H4.
  simpl.
  omega.
Qed.

(* definition of mapstos' *)

Definition mapstos' (e:expr) (lst:list Z) :=
  sep.mapstos e (map (fun x => int_e x) lst).

Notation "x '|--->' l" := (mapstos' x l) (at level 80).

Lemma inde_mapstos' : forall lst l p,
  inter (expr_var p) l nil ->
  inde l (p |---> lst).
  intros.
  unfold mapstos'.
  apply inde_mapstos; auto.
  rewrite map_expr_var_list_Z.
  rewrite fold_right_app_map_nil.
  apply inter_sym.
  apply inter_nil.
  intros.
  generalize (in_map' _ _ _ _ _ H0); intro.
  inversion_clear H1.
  inversion_clear H2.
  rewrite H3.
  auto.
Qed.

Lemma mapstos'_app_sepcon: forall l1 l2 st s h,
  (st |---> l1 ++ l2) s h ->
  ((st |---> l1) ** ((st +e (nat_e (length l1))) |---> l2)) s h.
  induction l1; simpl; intros.
  unfold mapstos' at 1.
  simpl.
  rewrite sep.con_com_equiv.
  apply sep.con_emp'.
  red in H.
  red.
  eapply mapstos_equiv.
  apply H.
  simpl.
  rewrite <-Zplus_0_r_reverse.
  reflexivity.
  red in H.
  simpl in H.
  Decompose_sepcon H h1 h2.
  generalize (IHl1 _ _ _ _ H3); clear H3; intros.
  Decompose_sepcon H2 h21 h22.
  Compose_sepcon (h1 +++ h21) h22.
  red; simpl.
  Compose_sepcon h1 h21.
  assumption.
  assumption.
  red in H6.
  red.
  eapply mapstos_equiv.
  apply H6.
  simpl.
  rewrite <- Z_of_nat_Zpos_P_of_succ_nat.
  rewrite inj_plus.
  simpl Z_of_nat.
  ring.
Qed.

Lemma mapstos'_cons_sepcon: forall a l st s h,
  (st |---> a::l) s h ->
  ((st |-> int_e a) ** ((st +e (nat_e 1)) |---> l)) s h.
  intros.
  cutrewrite (a::l = (a::nil)++l) in H; [idtac | auto].
  generalize (mapstos'_app_sepcon _ _ _ _ _ H); intro.
  simpl in H0.
  unfold mapstos' at 1 in H0.
  simpl in H0.
  Decompose_sepcon H0 h1 h2.
  Compose_sepcon h1 h2.
  apply sep.con_emp.
  assumption.
  assumption.
Qed.

Lemma mapstos'_sepcon_app: forall l1 l2 st s h,
  ((st |---> l1) ** ((st +e (nat_e (length l1))) |---> l2)) s h ->
  (st |---> l1 ++ l2) s h.
  induction l1.
  simpl; intros.
  Decompose_sepcon H h1 h2.
  red in H0.
  simpl in H0.
  red in H0.
  assert (h2 = h).
  subst h1.
  Equal_heap.
  rewrite <- H2; auto.
  red in H3; red; eapply mapstos_equiv.
  apply H3.
  simpl.
  omega.
  simpl; intros.
  Decompose_sepcon H h1 h2.
  red in H0; simpl in H0.
  Decompose_sepcon H0 h11 h12.
  red; simpl.
  Compose_sepcon h11 (h12 +++ h2).
  auto.
  red in IHl1.
  apply IHl1.
  Compose_sepcon h12 h2. 
  red.
  eapply mapstos_equiv.
  apply H6.
  auto.
  red in H3; red.
  eapply mapstos_equiv.
  eapply H3.
  cutrewrite (S (length l1) = length l1 + 1)%nat.
  simpl.
  rewrite inj_plus.
  simpl Z_of_nat.
  ring.
  omega.
Qed.   

(* definition of strings *)

Definition string' (lst:list nat) := ~ In O lst.

Definition string (lst:list Z) := 
  exists lst',
    string' lst' /\
    lst = (map (fun x => Z_of_nat x) lst') ++ (0::nil).

Lemma string_nil : ~ string nil.
  intro.
  red in H.
  inversion_clear H.
  inversion_clear H0.
  assert (1 <= length (@nil Z))%nat.
  rewrite H1.
  rewrite length_app.
  simpl.
  omega.
  inversion H0.
Qed.

Lemma string'_sub : forall lst, 
  string' lst ->
  string' (tail lst).
  induction lst; intros; auto.
  simpl.
  red in H.
  red.
  simpl in H.
  tauto.
Qed.

Lemma string_sub : forall lst, 
  (2 <= length lst)%nat ->
  string lst ->
  string (tail lst).
  induction lst; intros; auto.
  simpl.
  red in H0.
  inversion_clear H0.
  inversion_clear H1.
  red.
  exists (tail x).
  split.
  apply string'_sub; auto.
  destruct x.
  simpl in H2.
  rewrite H2 in H.
  inversion H.
  inversion H3.
  simpl.
  simpl in H2.
  injection H2; auto.
Qed.

Lemma string_sup : forall lst, 
  string lst ->
  forall lst',
    string' lst' ->
    string (map (fun x => Z_of_nat x) lst' ++ lst).
  induction lst'.
  simpl.
  auto.
  simpl.
  intros.
  generalize (string'_sub _ H0); intro.
  simpl in H1.
  generalize (IHlst' H1); intro.
  red in H2.
  inversion_clear H2 as [lst''].
  red.
  exists (a::lst'').
  inversion_clear H3.
  split.
  red.
  red in H2.
  red in H0.
  simpl in H0.
  simpl.
  tauto.
  simpl.
  rewrite H4.
  reflexivity.
Qed.

Lemma string_last : forall lst, string lst ->
  forall i, nth i lst (-1) = 0 ->
    (i = length lst - 1)%nat.
  induction lst; intros.
  generalize string_nil; tauto.
  simpl.
  rewrite <- minus_n_O.
  destruct lst.
  red in H.
  inversion_clear H.
  inversion_clear H1.
  destruct x.
  simpl in H2.
  injection H2; clear H2; intro.
  subst a.
  simpl in H0.
  destruct i; auto.
  destruct i; discriminate.
  assert (2 <= length (a::nil))%nat.
  rewrite H2.
  rewrite length_app.
  simpl.
  rewrite map_length.
  omega.
  inversion H1.
  inversion H4.
  destruct i.
  simpl in H0.
  subst a.
  red in H.
  inversion_clear H.
  inversion_clear H0.
  destruct x.
  simpl in H1.
  discriminate.
  simpl in H1.
  injection H1; clear H1; intros.
  assert (n=O).
  omega.
  subst n.
  red in H.
  simpl in H.
  tauto.
  assert (string (z :: lst)).
  cutrewrite (z::lst = tail (a::z::lst)); [idtac | auto].
  apply string_sub.
  simpl.
  omega.
  assumption.
  lapply (IHlst H1 i).
  intros.
  rewrite H2.
  simpl.
  rewrite <- minus_n_O.
  reflexivity.
  simpl in H0.
  simpl.
  assumption.
Qed.

Lemma string_hd_ge0: forall a l,
  string (a::l) ->
  a >= 0.
  intros.
  inversion_clear H.
  inversion_clear H0.
  destruct x.
  injection H1.
  intros.
  omega.
  simpl in H1.
  injection H1.
  intros.
  omega.
Qed.

Lemma string_last' : forall i lst, 
  string lst ->
  (i = length lst - 1)%nat ->
  nth i lst (-1) = 0.
  intros.
  red in H.
  inversion_clear H as [lst'].
  inversion_clear H1.
  rewrite H2.
  rewrite H2 in H0.
  rewrite length_app in H0.
  simpl in H0.
  rewrite nth_app.
  rewrite H0.
  cutrewrite ((length (map (fun x : nat => Z_of_nat x) lst') + 1 - 1 -
    length (map (fun x : nat => Z_of_nat x) lst')) = 0)%nat.
  simpl.
  reflexivity.
  generalize (length (map (fun x : nat => Z_of_nat x) lst')).
  intros.
  omega.
  rewrite H0.
  omega.
Qed.

Lemma string_last'' : forall i lst, 
  string lst ->
  (i < length lst)%nat ->
  nth i lst (-1) >= 0.
  induction i; intros.
  red in H.
  inversion_clear H as [lst'].
  inversion_clear H1.
  destruct lst'.
  simpl in H2.
  rewrite H2.
  simpl.
  omega.
  rewrite H2.
  simpl.
  red in H.
  simpl in H.
  omega.
  inversion_clear H as [lst'].
  inversion_clear H1.
  destruct lst.
  destruct lst'; discriminate.
  simpl.
  apply IHi.
  destruct lst'; try discriminate.
  simpl in H2.
  destruct lst; try discriminate.
  simpl in H0.
  inversion H0.
  inversion H3.
  simpl in H2.
  injection H2; clear H2; intros.
  subst z.
  rewrite H1.
  red.
  exists lst'.
  split; auto.
  generalize (string'_sub _ H); intro.
  auto.
  simpl in H0.
  omega.
Qed.

Definition c1 := O.
Definition c2 := 1%nat.
Definition buf := 2%nat.
Definition str := 3%nat.
Definition str_tmp := 4%nat.

Hint Unfold c1 c2 buf str str_tmp.

Lemma StringCopy_specif : forall buf_lst str_lst
  (Hbuf: (0 < length buf_lst)%nat)
  (Hbuf2: (length str_lst <= length buf_lst)%nat)
  (Hstr: string str_lst),
  {{ (var_e buf |---> buf_lst) ** (var_e str |---> str_lst) }}
  StringCopy c1 c2 buf str str_tmp 
  {{ (var_e buf |---> str_lst) ** TT ** (var_e str |---> str_lst) }}.
  intros.
  unfold StringCopy.

  apply semax_assign'' with (fun s h =>
    ((var_e buf |---> buf_lst) ** (var_e str |---> str_lst)) s h /\ store.lookup c1 s = store.lookup buf s).
  red; intros; red.
  split.
  apply inde_update_store.
  apply inde_sep_con.
  apply inde_mapstos'.
  apply inter_weak.
  apply inter_nil.
  intro X; simpl in X.
  inversion_clear X; try discriminate||auto.
  apply inde_mapstos'.
  apply inter_weak.
  apply inter_nil.
  intro X; simpl in X.
  inversion_clear X; try discriminate||auto.
  assumption.
  rewrite store.lookup_update'.
  elim store.lookup_update.
  reflexivity.
  intro; discriminate.

  apply semax_assign'' with (fun s h =>
    ((var_e buf |---> buf_lst) ** (var_e str |---> str_lst)) s h /\ 
    store.lookup c1 s = store.lookup buf s /\ store.lookup c2 s = store.lookup str s).
  red; intros; red.
  split.
  apply inde_update_store.
  apply inde_sep_con.
  apply inde_mapstos'.
  apply inter_weak.
  apply inter_nil.
  intro X; simpl in X.
  inversion_clear X; try discriminate||auto.
  apply inde_mapstos'.
  apply inter_weak.
  apply inter_nil.
  intro X; simpl in X.
  inversion_clear X; try discriminate||auto.
  tauto.
  elim store.lookup_update.
  elim store.lookup_update.
  rewrite store.lookup_update'.
  elim store.lookup_update.
  tauto.
  intro; discriminate.
  intro; discriminate.
  intro; discriminate.

  destruct str_lst as [_ | str0 str_lst].
  generalize string_nil; contradiction.

  apply semax_lookup_backwards''2 with (fun s h =>
     ((var_e buf |---> buf_lst) ** (var_e str |---> str0 :: str_lst)) s h /\
     store.lookup c1 s = store.lookup buf s /\
     store.lookup c2 s = store.lookup str s /\
     store.lookup str_tmp s = str0
  ).
  red; intros.
  exists (int_e str0).
  split.
  decompose [and] H; clear H.
  Decompose_sepcon H0 h1 h2.
  unfold mapstos' in H5.
  simpl in H5.
  Decompose_sepcon H5 h21 h22.
  exists h21; exists (h1+++h22).
  split.
  Disjoint_heap.
  split.
  Equal_heap.
  unfold TT; split; auto.
  eapply mapsto_equiv.
  apply H5.
  simpl.
  auto.
  reflexivity.
  red.
  split.
  apply inde_update_store.
  apply inde_sep_con.
  apply inde_mapstos'.
  simpl.
  apply inter_weak.
  apply inter_nil.
  intro X; simpl in X.
  inversion_clear X; try discriminate||auto.
  apply inde_mapstos'.
  simpl.
  apply inter_weak.
  apply inter_nil.
  intro X; simpl in X.
  inversion_clear X; try discriminate||auto.
  tauto.
  elim store.lookup_update.
  elim store.lookup_update.
  rewrite store.lookup_update'.
  elim store.lookup_update.
  elim store.lookup_update.
  split; try tauto.
  intro; discriminate.
  intro; discriminate.
  intro; discriminate.
  intro; discriminate.

  apply semax_strengthen_pre with (fun s h => exists i,
    (var_e buf |---> (heads (str0::str_lst) i)++(del_heads buf_lst i) ** (var_e str |---> str0 :: str_lst)) s h /\
    store.lookup c1 s = store.lookup buf s + Z_of_nat i /\
    store.lookup c2 s = store.lookup str s + Z_of_nat i /\
    store.lookup str_tmp s = nth i (str0::str_lst) (-1) /\
    (i <= length (str0 :: str_lst))%nat /\
    store.lookup str_tmp s >= 0
  ).

  red; intros.
  exists O.
  decompose [and] H; clear H.
  split.
  simpl del_heads.
  simpl heads.
  simpl app.
  tauto.
  simpl Z_of_nat.
  do 2 rewrite <-Zplus_0_r_reverse.
  simpl nth.
  split; auto.
  split; auto.
  split; auto.
  split; try omega.
  generalize (string_hd_ge0 _ _ Hstr); intros.
  rewrite H4; auto.

  
  apply semax_seq with (fun s h => 
    (exists i,
      (var_e buf |---> (heads (str0::str_lst) i)++(del_heads buf_lst i) ** (var_e str |---> str0 :: str_lst)) s h /\
      store.lookup c1 s = store.lookup buf s + Z_of_nat i /\
      store.lookup c2 s = store.lookup str s + Z_of_nat i /\
      store.lookup str_tmp s = nth i (str0::str_lst) (-1) /\
      (i <= length (str0 :: str_lst))%nat /\
      store.lookup str_tmp s >= 0
    ) /\
    eval_b (var_e str_tmp =/= int_e 0) s = false
  ).

  apply semax_while with (P:=fun s h => 
    exists i,
      (var_e buf |---> (heads (str0::str_lst) i)++(del_heads buf_lst i) ** (var_e str |---> str0 :: str_lst)) s h /\
      store.lookup c1 s = store.lookup buf s + Z_of_nat i /\
      store.lookup c2 s = store.lookup str s + Z_of_nat i /\
      store.lookup str_tmp s = nth i (str0::str_lst) (-1) /\
      (i <= length (str0 :: str_lst))%nat /\
      store.lookup str_tmp s >= 0
  ).

  eapply semax_mutation_backwards'' with (
    fun s h => 
    exists i,
      (var_e buf |---> (heads (str0::str_lst) (i + 1))++(del_heads buf_lst (i + 1)) ** (var_e str |---> str0 :: str_lst)) s h /\
      store.lookup c1 s = store.lookup buf s + Z_of_nat i /\
      store.lookup c2 s = store.lookup str s + Z_of_nat i /\
      store.lookup str_tmp s = nth i (str0::str_lst) (-1) /\
      store.lookup str_tmp s > 0 /\
      (i+1 < length (str0 :: str_lst))%nat).
  red; intros.
  inversion_clear H.
  inversion_clear H0.
  decompose [and] H; clear H.
  
  (* is (del_heads buf_lst i) the empty heap ? *)

  assert (length buf_lst <= x \/ length buf_lst > x)%nat; [omega | idtac].

  (* It depend if the size of buf_lst is larger than i  *)
  
  inversion_clear H.

  (* if the size of the buffer is lesser or equal, that means that we are trying to write outside buf_lst ... *)

  rewrite (del_heads_all) in H0; try omega.
  
  (* ... mutation cannot be performed !!!! but we can build a contradiction with H5, Hbuf2, H4 and H6 *)

  assert (length buf_lst = length (str0::str_lst)).
  omega.
  rewrite H in H6.
  assert (x = length (str0::str_lst)).
  omega.

  assert (store.lookup str_tmp s = -1).
  

  rewrite H8 in H4.
  rewrite nth_last in H4.
  auto.
  auto.
  
  rewrite H9 in H7.

  (* So this case is impossible *)

  assert (False); [omega | contradiction].
  assert (store.lookup str_tmp s > 0).
  Eval_b_hyp H1.
  omega.
  assert ((x + 1) = length (str0 :: str_lst) \/ x = length (str0 :: str_lst) \/ x + 1 < length (str0 :: str_lst))%nat; try omega.
  inversion_clear H8.
  rewrite string_last' in H4.
  Eval_b_hyp H1.
  tauto.
  auto.
  omega.
  inversion_clear H9.
  subst x.
  rewrite nth_last in H4; auto.
  rewrite H4 in H.
  assert (False); [omega | contradiction].

  rewrite (del_heads_destruct buf_lst x (-1)) in H0; try omega.
  Decompose_sepcon H0 h1 h2.
  generalize (mapstos'_app_sepcon _ _ _ _ _ H9); clear H9; intros.
  Decompose_sepcon H9 h11 h12.
  generalize (mapstos'_cons_sepcon _ _ _ _ _ H15); clear H15; intros.
  Decompose_sepcon H14 h121 h122.
  exists (int_e (nth x buf_lst (-1))).
  Compose_sepcon h121 (h2 +++ h11 +++ h122).
  Mapsto.
  rewrite H3.
  rewrite (length_heads (length (str0 :: str_lst))).
  auto.
  auto.
  auto.
  Intro_sepimp h121' h'.
  exists x.
  split; auto.
  Compose_sepcon (h11 +++ h121' +++ h122) h2; auto.
  eapply mapstos'_sepcon_app.
  Compose_sepcon (h11 +++ h121') h122.
  rewrite (heads_destruct) with (a := -1).
  eapply mapstos'_sepcon_app.
  Compose_sepcon h11 h121' .
  auto.
  Opaque nth.
  red.
  simpl map.
  red.
  Transparent nth.
  Compose_sepcon h121' heap.emp.
  Mapsto.
  rewrite H3.
  rewrite length_heads with (n:= length (str0 :: str_lst)).
  auto.
  auto.
  auto.
  red; auto.

  omega.

  red in H18; red.
  eapply mapstos_equiv.
  apply H18.
  simpl.  
  rewrite length_heads with (n := length (str0 :: str_lst)); try omega.
  rewrite length_heads with (n := length (str0 :: str_lst)); try omega.
  rewrite inj_plus.
  simpl Z_of_nat.
  ring.
  
  eapply semax_assign'' with   (
    fun s h => 
      exists i,
        (var_e buf |---> (heads (str0::str_lst) (i + 1))++(del_heads buf_lst (i + 1)) ** (var_e str |---> str0 :: str_lst)) s h /\
        store.lookup c1 s = store.lookup buf s + (Z_of_nat i) + 1 /\
        store.lookup c2 s = store.lookup str s + (Z_of_nat i) /\
        store.lookup str_tmp s = nth i (str0::str_lst) (-1) /\
        store.lookup str_tmp s > 0 /\
        (i+1 < length (str0 :: str_lst))%nat
  ).

  red; intros.
  inversion_clear H.
  decompose [and] H0; clear H0.
  red.
  exists x.
  split.
  apply inde_update_store.
  apply inde_sep_con.
  apply inde_mapstos'.
  apply inter_weak.
  apply inter_nil.
  intro X; simpl in X.
  inversion_clear X; try discriminate||auto.
  apply inde_mapstos'.
  simpl.
  apply inter_weak.
  apply inter_nil.
  intro X; simpl in X.
  inversion_clear X; try discriminate||auto.
  tauto.
  rewrite store.lookup_update'.
  elim store.lookup_update.
  elim store.lookup_update.
  elim store.lookup_update.
  elim store.lookup_update.
  split.
  simpl.
  rewrite H2; auto.
  tauto.
  intro; discriminate.
  intro; discriminate.
  intro; discriminate.
  intro; discriminate.
  
  eapply semax_assign'' with   (
    fun s h => 
      exists i,
        (var_e buf |---> (heads (str0::str_lst) (i + 1))++(del_heads buf_lst (i + 1)) ** (var_e str |---> str0 :: str_lst)) s h /\
        store.lookup c1 s = store.lookup buf s + (Z_of_nat i) + 1 /\
        store.lookup c2 s = store.lookup str s + (Z_of_nat i) + 1 /\
        store.lookup str_tmp s = nth i (str0::str_lst) (-1) /\
        store.lookup str_tmp s > 0 /\
        (i+1 < length (str0 :: str_lst))%nat
  ).

  red; intros.
  inversion_clear H.
  decompose [and] H0; clear H0.
  red.
  exists x.
  split.
  apply inde_update_store.
  apply inde_sep_con.
  apply inde_mapstos'.
  apply inter_weak.
  apply inter_nil.
  intro X; simpl in X.
  inversion_clear X; try discriminate||auto.
  apply inde_mapstos'.
  simpl.
  apply inter_weak.
  apply inter_nil.
  intro X; simpl in X.
  inversion_clear X; try discriminate||auto.
  tauto.
  elim store.lookup_update.
  rewrite store.lookup_update'.
  elim store.lookup_update.
  elim store.lookup_update.
  elim store.lookup_update.
  split; auto.
  split.
  simpl; rewrite H1; auto.
  tauto.
  intro; discriminate.
  intro; discriminate.
  intro; discriminate.
  intro; discriminate.

  (* i = i + 1  *)

  eapply semax_lookup_backwards'.
  red; intros.
  inversion_clear H.
  decompose [and] H0; clear H0.
  exists (int_e (nth (x + 1) (str0 :: str_lst) (-1))).
  apply cell_read.
  split.
  Decompose_sepcon H h1 h2.

  generalize (heads_del_heads _ (length (str0 :: str_lst)) (str0 :: str_lst) (refl_equal _)  (x + 1)%nat); intros.
  rewrite H7 in H8; try omega.
  clear H7.
  
  generalize (mapstos'_app_sepcon _ _ _ _ _ H8); clear H8; intros.
  Decompose_sepcon H7 h21 h22.  
  

  rewrite (del_heads_destruct) with (a := -1) in H11; try omega.  

  generalize (mapstos'_cons_sepcon _ _ _ _ _ H11); clear H11; intros.
  Decompose_sepcon H10 h221 h222.
  Compose_sepcon h221 (h222 +++ h21 +++ h1).
  Mapsto.
  rewrite H1.
  rewrite (length_heads) with (n := length (str0 :: str_lst)); try omega.
  rewrite inj_plus; simpl Z_of_nat; ring.
  red; auto.

  red.
  exists (x + 1)%nat.
  split.
  apply inde_update_store.
  apply inde_sep_con.
  apply inde_mapstos'.
  apply inter_weak.
  apply inter_nil.
  intro X; simpl in X.
  inversion_clear X; try discriminate||auto.
  apply inde_mapstos'.
  apply inter_weak.
  apply inter_nil.
  intro X; simpl in X.
  inversion_clear X; try discriminate||auto.
  tauto.
  split.
  elim store.lookup_update.
  elim store.lookup_update.
  rewrite inj_plus.
  simpl Z_of_nat.
  rewrite H2.
  intuition.
  intro; discriminate.
  intro; discriminate.
  split.
  elim store.lookup_update.
  elim store.lookup_update.
  rewrite H1.
  rewrite inj_plus.
  simpl Z_of_nat.
  intuition.
  intro; discriminate.
  intro; discriminate.
  split.
  rewrite store.lookup_update'.
  Opaque nth.
  simpl.
  Transparent nth.
  auto.
  split; auto.
  omega.
  rewrite store.lookup_update'.
  Opaque nth.
  simpl.
  Transparent nth.

  eapply string_last''.
  auto.
 
  omega.
  

  eapply semax_mutation_backwards'.
  red; intros.
  inversion_clear H.
  inversion_clear H0.
  decompose [and] H; clear H.
  Decompose_sepcon H0 h1 h2.
  assert (store.lookup str_tmp s = 0).
  Eval_b_hyp_clean.
  unfold val.
  omega.
  assert (x = length (str0::str_lst) - 1)%nat.
  apply string_last.
  auto.
  rewrite <- H4; rewrite H8; auto.  

  rewrite del_heads_destruct with (a := -1) in H0.

  generalize (mapstos'_app_sepcon _ _ _ _ _ H0); clear H0; intros.
  Decompose_sepcon H0 h11 h12.

  generalize (mapstos'_cons_sepcon _ _ _ _ _ H14); clear H14; intros.
  Decompose_sepcon H13 h121 h122.
  
  exists (int_e (nth x buf_lst (-1))).
  Compose_sepcon h121 (h122 +++ h11 +++ h2).
  Mapsto.
  rewrite length_heads with (n := length (str0 :: str_lst)).
  rewrite H3.
  auto.
  auto.
  omega.
  Intro_sepimp h121' h'.
  Compose_sepcon (h122 +++ h11 +++ h121') h2; auto.
  Compose_sepcon (h11 +++ h121') h122 .

  rewrite heads_last with (i := x) (l := str0 :: str_lst); try omega.
  
  eapply mapstos'_sepcon_app.
  Compose_sepcon h11 h121'.
  auto.
  Opaque nth.
  red; simpl.
  Transparent nth.
  Compose_sepcon h121' heap.emp.
  Mapsto.
  rewrite H3.
  rewrite length_heads with (n := length (str0 :: str_lst)).
  auto.
  auto.
  omega.

  red; auto.
  intro; discriminate.

  red; auto.
  
  omega.
Qed.
  
End StringCopy.
