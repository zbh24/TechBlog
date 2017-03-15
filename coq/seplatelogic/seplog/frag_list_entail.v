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

(* TODO: shouldn't this go to heap.v? though maybe not in the interface... *)
Lemma singl_disjoint_neq: forall e1 e2 e3 e4 h1 h2 s,
  (e1 |-> e2) s h1 ->
  (e3 |-> e4) s h2 ->
  h1 # h2 ->
  eval e1 s <> eval e3 s.
  intros.
  inversion_clear H; inversion_clear H0.
  inversion_clear H2; inversion_clear H.
  subst h1 h2.
  generalize (heap.disjoint_singleton' _ _ _ _ H1); intro.
  swap H.
  rewrite H3 in H0.
  rewrite H2 in H0; auto.
Qed.  

(*
 * Definition and properties of lists
 *)
(* Definition generale a extraire dans un fichier *)

Inductive Lst : expr -> expr -> store.s -> heap.h -> Prop :=
  | Lst_end: forall e1 e2 s h,
    eval e1 s = eval e2 s ->
    sep.emp s h ->
    Lst e1 e2 s h
  | Lst_suiv: forall e1 e2 e3 e4 s h h1 h2,
    h1 # h2 -> h = h1 +++ h2 ->
    eval e1 s <> eval e3 s ->
    eval e1 s <> 0%Z ->
    eval (e1 +e nat_e 1) s <> 0%Z ->
    (e1 |-> e2 ** (e1 +e nat_e 1 |-> e4)) s h1 ->
    Lst e2 e3 s h2 ->
    Lst e1 e3 s h.

Lemma Lst_equiv': forall s  h e1 e2,
  Lst e1 e2 s h ->
  forall e3 e4 s',
    eval e1 s = eval e3 s' ->
    eval e2 s = eval e4 s' ->
    Lst e3 e4 s' h.
  do 5 intro.
  induction H; intros.
  constructor 1; auto||omega.
  econstructor 2 with (int_e (eval e2 s)) (int_e (eval e4 s)) h1 h2; try auto||omega.
  simpl; simpl in H3; omega.
  Decompose_sepcon H4 h11 h12.
  Compose_sepcon h11 h12; Mapsto.
Qed.

Lemma Lst_equiv: forall s h e1 e2,
  Lst e1 e2 s h ->
  forall e3 e4,
    eval e1 s = eval e3 s ->
    eval e2 s = eval e4 s ->
    Lst e3 e4 s h.
  intros.
  eapply Lst_equiv'.
  apply H.
  auto.
  auto.
Qed.

Lemma Lst_app : forall e1 e2 s h1,
  Lst e1 e2 s h1 ->
  forall e3 h2 h3 h,
    Lst e2 e3 s h2 ->
    (exists v, (e3 |-> int_e v) s h3) ->
    h1 # h2 ->
    h1 # h3 ->
    h = h1 +++ h2  ->
    Lst e1 e3 s h.
  do 5 intro.
  induction H; intros.
  red in H0.
  subst h.
  symmetry in H5.
  rewrite heap.union_com in H5.
  rewrite heap.equal_union_emp in H5.
  subst h2.
  clear H3 H4.
  eapply Lst_equiv.
  apply H1.
  auto.
  auto.
  apply heap.disjoint_com.
  apply heap.disjoint_emp.
  apply Lst_suiv with (h1 := h1) (h2 := h2 +++ h0) (e2 := e2) (e4 := e4); auto.
  Disjoint_heap.
  Equal_heap.
  Decompose_sepcon H4 h11 h12.
  inversion_clear H7.
  eapply singl_disjoint_neq.
  apply H11.
  apply H13.
  Disjoint_heap.
  eapply IHLst.
  apply H6.
  apply H7.
  Disjoint_heap.
  Disjoint_heap.
  Equal_heap.
Qed.

Lemma Lst_app' : forall e1 e2 s h1,
  Lst e1 e2 s h1 ->
  forall e3 h2 h,
    Lst e2 e3 s h2 ->
    h1 # h2 ->
    h = h1 +++ h2  ->
    eval e3 s = 0%Z ->
    Lst e1 e3 s h.
  do 5 intro.
  induction H; intros.
  red in H0.
  subst h.
  symmetry in H3.
  rewrite heap.union_com in H3.
  rewrite heap.equal_union_emp in H3.
  subst h2.
  clear H2.
  eapply Lst_equiv.
  apply H1.
  auto.
  auto.
  auto.
  apply Lst_suiv with (h1 := h1) (h2 := h2 +++ h0) (e2 := e2) (e4 := e4); auto.
  Disjoint_heap.
  Equal_heap.
  rewrite H9; auto.
  eapply IHLst; auto.
  auto.
  Disjoint_heap.
Qed.

(*
 * Syntax and semantics of formulas
 *)

(* a Pi formula is a boolean expression *)
Definition Pi := expr_b.

Definition eval_pi := eval_b.

(* a Sigma formula is a spatial formula composed of the following connectives *)
Inductive Sigma : Set :=
  | singl : expr -> expr -> Sigma
  | cell : expr -> Sigma
  | emp : Sigma
  | star : Sigma -> Sigma -> Sigma
  | lst : expr -> expr -> Sigma.

(* Definition generale a extraire dans un fichier *)
Fixpoint Sigma_interp (a : Sigma) : assert :=
  match a with
    singl e1 e2 => fun s h => (e1 |-> e2) s h /\ eval e1 s <> 0%Z
    | emp => sep.emp
    | star s1 s2 => Sigma_interp s1 ** Sigma_interp s2
    | cell e => fun s h => (exists v, (e |-> int_e v) s h) /\ eval e s <> 0%Z
    | lst e1 e2 => Lst e1 e2
  end.

(* an assrt is a couple of a Pi and a Sigma formula *)
Definition assrt := prod Pi Sigma.

Definition assrt_interp (a : assrt) : assert :=
  match a with
    (pi, sigm) => fun s h => eval_pi pi s = true /\ Sigma_interp sigm s h
  end.

(* an Assrt is a disjunction of assrts *)
Definition Assrt := list assrt.

Fixpoint Assrt_interp (l : Assrt) : assert := 
  match l with 
    | nil => fun s h => False
    | hd :: tl => fun s h => assrt_interp hd s h \/ Assrt_interp tl s h
  end.

(*
 * A proof system for assrt entailment 
 *)

Notation "s ** t" := (star s t) (at level 80) : tmp_scope.

Open Local Scope tmp_scope.

Inductive entail : assrt -> assrt -> Prop :=

(* final rules *)

| entail_incons : forall pi1 pi2 sig1 sig2, 
  (forall s, eval_pi pi1 s = true -> False) -> 
  entail (pi1, sig1) (pi2, sig2)

| entail_tauto : forall pi1 pi2, 
  (forall s, eval_pi pi1 s = true -> eval_pi pi2 s = true) -> 
  entail (pi1, emp) (pi2, emp)

    (* structural rules *)

| entail_coml : forall pi1 sig1 sig2 L,
  entail (pi1, sig2 ** sig1) L ->
  entail (pi1, sig1 ** sig2) L

| entail_comr : forall pi1 sig1 sig2 L,
  entail L (pi1, sig2 ** sig1)  ->
  entail L (pi1, sig1 ** sig2)

| entail_assocl : forall pi1 sig1 sig2 sig3 L,
  entail (pi1, (sig1 ** sig2) ** sig3) L ->
  entail (pi1, sig1 ** (sig2 ** sig3)) L

| entail_assocr : forall pi1 sig1 sig2 sig3 L,
  entail L (pi1, (sig1 ** sig2) ** sig3)  ->
  entail L (pi1, sig1 ** (sig2 ** sig3))

| entail_epseliml : forall pi1 sig1 L,
  entail (pi1, sig1) L ->
  entail (pi1, sig1 ** emp) L

| entail_epselimr : forall pi1 sig1 L,
  entail L (pi1, sig1) ->
  entail L (pi1, sig1 ** emp)

| entail_empintrol : forall pi1 sig1 L,
  entail (pi1, sig1 ** emp) L ->
  entail (pi1, sig1) L

| entail_empintror : forall pi1 sig1 L,
  entail L (pi1, sig1 ** emp) ->
  entail L (pi1, sig1)
  
    (* elimination rules for list *)    

| entail_lstnilelimr : forall pi1 sig1 pi2 sig2 e1 e2,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e2) s = true) -> 
  entail (pi1, sig1) (pi2, sig2) ->
  entail (pi1, sig1) (pi2, sig2 ** (lst e1 e2))

  (* TODO: constructor not used anywhere *)
| entail_lstnileliml : forall pi1 sig1 pi2 sig2 e1 e2,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e2) s = true) -> 
  entail (pi1, sig1) (pi2, sig2) ->
  entail (pi1, sig1 ** (lst e1 e2)) (pi2, sig2)

| entail_lstsamelst : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e3) s = true) -> 
  (forall s, eval_pi pi1 s = true -> eval_pi (e2 == e4) s = true) -> 
  entail (pi1, sig1) (pi2, sig2) ->
  entail (pi1, sig1 ** (lst e1 e2)) (pi2, sig2 ** (lst e3 e4))

| entail_lstelim : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e3) s = true) -> 
  entail (pi1, sig1 ** (cell e4)) (pi2, sig2 ** (lst e2 e4)) ->
  entail (pi1, (sig1 ** (cell e4)) ** (lst e1 e2)) (pi2, sig2 ** (lst e3 e4))

| entail_lstelim_v2 : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4 sig1',
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e3) s = true) -> 
  entail (pi1, sig1) (pi1, (sig1' ** (cell e4))) ->
  entail (pi1, sig1' ** (cell e4)) (pi2, sig2 ** (lst e2 e4)) ->    
  entail (pi1, sig1 ** (lst e1 e2)) (pi2, sig2 ** (lst e3 e4))

| entail_lstelim' : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4 e5,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e3) s = true) -> 
  (forall s, eval_pi pi1 s = true -> eval_pi (e4 =/= e5) s = true) -> 
  entail (pi1, sig1 ** (lst e4 e5)) (pi2, sig2 ** (lst e2 e4)) ->
  entail (pi1, (sig1 ** (lst e4 e5)) ** (lst e1 e2)) (pi2, sig2 ** (lst e3 e4))

| entail_lstelim'_v2 : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4 e5 sig1',
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e3) s = true) -> 
  entail (pi1, sig1) (pi1, sig1' ** (lst e4 e5)) ->
  (forall s, eval_pi pi1 s = true -> eval_pi (e4 =/= e5) s = true) -> 
  entail (pi1, sig1' ** (lst e4 e5)) (pi2, sig2 ** (lst e2 e4)) ->    
  entail (pi1, sig1 ** (lst e1 e2)) (pi2, sig2 ** (lst e3 e4))

| entail_lstelim'' : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e3) s = true) -> 
  (forall s, eval_pi pi1 s = true -> eval_pi (e4 == int_e 0%Z) s = true) -> 
  entail (pi1, sig1) (pi2, sig2 ** (lst e2 e4)) ->
  entail (pi1, sig1 ** (lst e1 e2)) (pi2, sig2 ** (lst e3 e4))

| entail_lstelim''' : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e3) s = true) -> 
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 =/= e4) s = true) -> 
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 =/= int_e 0%Z) s = true) -> 
  entail (pi1, sig1) (pi2, sig2 ** ((cell (e1 +e nat_e 1)) ** (lst e2 e4))) ->
  entail (pi1, sig1 ** (singl e1 e2)) (pi2, sig2 ** (lst e3 e4))

    (* rule to eliminate mapstos *)

| entail_star_elim : forall pi1 pi2 sig1 sig2 e1 e2 e3 e4,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e3) s = true) ->
  (forall s, eval_pi pi1 s = true -> eval_pi (e2 == e4) s = true) ->    
  entail (pi1, sig1) (pi2, sig2) ->
  entail (pi1, sig1 ** (singl e1 e2)) (pi2, sig2 ** (singl e3 e4))

| entail_star_elim': forall pi1 pi2 sig1 sig2 e1 e2 e3,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e3) s = true) ->
  entail (pi1, sig1) (pi2, sig2) ->
  entail (pi1, sig1 ** (singl e1 e2)) (pi2, sig2 ** (cell e3))

| entail_star_elim'': forall pi1 pi2 sig1 sig2 e1 e3,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 == e3) s = true) ->
  entail (pi1, sig1) (pi2, sig2) ->
  entail (pi1, sig1 ** (cell e1)) (pi2, sig2 ** (cell e3))

    (* rule to generate constraints *)

| entail_sepcon_neq : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  entail (pi1 &&& (e1 =/= e3), sig1 ** ((singl e1 e2) ** (singl e3 e4))) (pi2, sig2) ->
  entail (pi1, sig1 ** ((singl e1 e2) ** (singl e3 e4))) (pi2, sig2)

| entail_sepcon_neq' : forall pi1 sig1 pi2 sig2 e1 e2 e3,
  entail (pi1 &&& (e1 =/= e3), sig1 ** ((singl e1 e2) ** (cell e3))) (pi2, sig2) ->
  entail (pi1, sig1 ** ((singl e1 e2) ** (cell e3))) (pi2, sig2)

| entail_sepcon_neq'' : forall pi1 sig1 pi2 sig2 e1 e3,
  entail (pi1 &&& (e1 =/= e3), sig1 ** ((cell e1) ** (cell e3))) (pi2, sig2) ->
  entail (pi1, sig1 ** ((cell e1) ** (cell e3))) (pi2, sig2)

| entail_sepcon_neq''' : forall pi1 sig1 pi2 sig2 e1 e2 e3,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 =/= e2) s = true) ->
  entail (pi1 &&& (e1 =/= e3), sig1 ** ((lst e1 e2) ** (cell e3))) (pi2, sig2) ->
  entail (pi1, sig1 ** ((lst e1 e2) ** (cell e3))) (pi2, sig2)

| entail_sepcon_neq'''' : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 =/= e2) s = true) ->
  entail (pi1 &&& (e1 =/= e3), sig1 ** ((lst e1 e2) ** (singl e3 e4))) (pi2, sig2) ->
  entail (pi1, sig1 ** ((lst e1 e2) ** (singl e3 e4))) (pi2, sig2)

| entail_sepcon_neq''''': forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  (forall s, eval_pi pi1 s = true -> eval_pi (e1 =/= e2) s = true) ->
  (forall s, eval_pi pi1 s = true -> eval_pi (e3 =/= e4) s = true) ->
  entail (pi1 &&& (e1 =/= e3), sig1 ** ((lst e1 e2) ** (lst e3 e4))) (pi2, sig2) ->
  entail (pi1, sig1 ** ((lst e1 e2) ** (lst e3 e4))) (pi2, sig2)

| entail_singl_not_null : forall pi1 sig1 pi2 sig2 e1 e2,
  entail (pi1 &&& (e1 =/= (nat_e 0)), sig1 ** (singl e1 e2)) (pi2, sig2) ->
  entail (pi1, sig1 ** (singl e1 e2)) (pi2, sig2)

| entail_cell_not_null : forall pi1 sig1 pi2 sig2 e1,
  entail (pi1 &&& (e1 =/= (nat_e 0)), sig1 ** (cell e1)) (pi2, sig2) ->
  entail (pi1, sig1 ** (cell e1)) (pi2, sig2)

| entail_lst_not_null : forall pi1 sig1 pi2 sig2 e1 e2,
  (forall s, eval_pi pi1 s = true -> eval_pi (e2 =/= (nat_e 0)) s = true) ->
  entail (pi1 &&& (e1 =/= (nat_e 0)), sig1 ** (lst e1 e2)) (pi2, sig2) ->
  entail (pi1, sig1 ** (lst e1 e2)) (pi2, sig2)

(* nico: is entail_monotony really useful? *)
| entail_monotony : forall pi1 pi2 sig11 sig12 sig21 sig22,
  entail (pi1,sig11) (pi2, sig21) ->
  entail (pi1,sig12) (pi2, sig22) ->
  entail (pi1, sig11 ** sig12) (pi2, sig21 ** sig22)
  
| entail_destructlist: forall pi1 pi2 sig1 sig2 e1 e2,
  (entail (pi1 &&& (e1 == e2), sig1 ** (lst e1 e2)) (pi2, sig2)) ->
  (entail (pi1 &&& (e1 =/= e2), sig1 ** (lst e1 e2)) (pi2, sig2)) ->
  entail (pi1, star sig1 (lst e1 e2)) (pi2, sig2).

Notation "s '|--' t" := (entail s t) (at level 80) : tmp_scope.

(* derived rules *)

Lemma entail_id : forall sig pi,
  (pi, sig) |-- (pi, sig).
  induction sig; intros.

  eapply entail_empintror.
  eapply entail_empintrol.
  eapply entail_coml.
  eapply entail_comr.
  eapply entail_star_elim.
  intros; simpl; apply Zeq_bool_refl.
  intros; simpl; apply Zeq_bool_refl.
  apply entail_tauto; auto.

  eapply entail_empintror.
  eapply entail_empintrol.
  eapply entail_coml.
  eapply entail_comr.
  eapply entail_star_elim''.
  intros; simpl; apply Zeq_bool_refl.
  apply entail_tauto; auto.

  apply entail_tauto; auto.

  apply entail_monotony; auto.

  eapply entail_empintror.
  eapply entail_empintrol.
  eapply entail_coml.
  eapply entail_comr.
  eapply entail_lstsamelst.
  intros; simpl; apply Zeq_bool_refl.
  intros; simpl; apply Zeq_bool_refl.
  apply entail_tauto; auto.
Qed.

Lemma entail_star_elim_lst : forall pi1 sig1 pi2 sig2 e1 e2,
  (pi1, sig1) |-- (pi2, sig2) ->
  (pi1, sig1 ** (lst e1 e2)) |-- (pi2, sig2 ** (lst e1 e2)).
  intros.
  apply entail_lstsamelst; auto.
  intros; simpl; apply Zeq_bool_refl.
  intros; simpl; apply Zeq_bool_refl.
Qed.  

Lemma entail_star_elim_star : forall s pi1 sig1 pi2 sig2,
  (pi1, sig1) |-- (pi2, sig2) ->
  (pi1, sig1 ** s) |-- (pi2, sig2 ** s).
  induction s; intros.

  apply entail_star_elim; auto.
  intros; simpl; apply Zeq_bool_refl.
  intros; simpl; apply Zeq_bool_refl.

  apply entail_star_elim''; auto.
  intros; simpl; apply Zeq_bool_refl.

  apply entail_epseliml.
  apply entail_epselimr.
  auto.

  apply entail_assocr.
  apply entail_assocl.
  auto.
  
  apply entail_lstsamelst; auto.
  intros; simpl; apply Zeq_bool_refl.
  intros; simpl; apply Zeq_bool_refl.
Qed.

Close Local Scope tmp_scope.

(* Soundness of the proof system *)

Lemma entail_soundness : forall P Q, 
  entail P Q -> 
  assrt_interp P ==> assrt_interp Q.
  intros.
  induction H; red; simpl; intros.

  generalize (H s); tauto.

  generalize (H s); tauto.

  apply IHentail.
  simpl.
  rewrite sep.con_com_equiv.
  auto.

  simpl in IHentail.
  rewrite sep.con_com_equiv.
  apply IHentail; auto.

  apply IHentail.
  rewrite <- sep.con_assoc_equiv in H0.
  auto.

  simpl in IHentail.
  rewrite <- sep.con_assoc_equiv.
  auto.

  apply IHentail.
  simpl.
  split; try tauto.
  apply sep.con_emp.
  tauto.

  simpl in IHentail.
  generalize (IHentail s h H0); intro.
  split; try tauto.
  apply sep.con_emp'.
  tauto.
  
  apply IHentail.
  simpl.
  split; try tauto.
  apply sep.con_emp'.
  tauto.

  simpl in IHentail.
  generalize (IHentail s h H0); intro.
  split; try tauto.
  apply sep.con_emp.
  tauto.

  simpl in IHentail.
  generalize (IHentail s h H1); intro.
  split; try tauto.
  Compose_sepcon h heap.emp.
  tauto.
  apply Lst_end.
  generalize (H s); intro.
  simpl in H3.
  apply Zeq_bool_true.
  tauto.
  red; auto.

  simpl in IHentail.
  apply IHentail.
  split; try tauto.
  inversion_clear H1.
  Decompose_sepcon H3 h1 h2.
  destruct H6.
  red in H6.
  subst h0.
  rewrite heap.equal_union_emp in H4.
  subst h1.
  auto.
  assert (eval e1 s = eval e3 s).
  apply Zeq_bool_true.
  simpl in H.
  apply H.
  auto.
  contradiction.

  simpl in IHentail.
  inversion_clear H2.
  Decompose_sepcon H4 h1 h2.
  generalize (IHentail _ _ (conj H3 H4)); intro.
  inversion_clear H6.
  split; auto.
  Compose_sepcon h1 h2; auto.
  eapply Lst_equiv.
  apply H7.
  apply Zeq_bool_true.
  apply (H s); auto.
  apply Zeq_bool_true.
  apply (H0 s); auto.

  inversion_clear H1.
  simpl in IHentail.
  Decompose_sepcon H3 h1 h2.
  generalize (IHentail _ _ (conj H2 H3)); clear IHentail; intros.
  inversion_clear H5.
  Decompose_sepcon H8 h11 h12.
  split; auto.
  Compose_sepcon h11 (h12 +++ h2). 
  auto.
  Decompose_sepcon H3 h11' h12'.
  eapply Lst_app.
  eapply Lst_equiv.
  apply H6.
  apply Zeq_bool_true.
  apply (H s); auto.
  reflexivity.
  apply H11.
  apply H13.
  Disjoint_heap.
  Disjoint_heap.
  Equal_heap.

  simpl in IHentail1.
  simpl in IHentail2.
  inversion_clear H2.
  Decompose_sepcon H4 h1 h2.
  generalize (IHentail1 _ _ (conj H3 H4)); intros.
  inversion_clear H6.
  clear H8.
  generalize (IHentail2 _ _ (conj H3 H9)); intros.
  inversion_clear H6.
  split; auto.
  Decompose_sepcon H10 h11 h12.
  Compose_sepcon h11 (h12 +++ h2); auto.
  Decompose_sepcon H9 h11' h12'.
  eapply Lst_app.
  eapply Lst_equiv.
  apply H7.
  apply Zeq_bool_true.
  apply (H s); auto.
  reflexivity.
  apply H13.
  apply H15.
  Disjoint_heap.
  Disjoint_heap.
  Equal_heap.

  simpl in IHentail.
  inversion_clear H2.
  Decompose_sepcon H4 h1 h2.
  generalize (IHentail _ _ (conj H3 H4)); intro.
  inversion_clear H6.
  split; auto.
  Decompose_sepcon H9 h11 h12.
  Compose_sepcon h11 (h12 +++ h2); auto.
  Decompose_sepcon H4 h11' h12'.
  inversion H15.
  generalize (H0 s H3); intro.
  simpl in H21.
  rewrite H14 in H21.
  rewrite Zeq_bool_refl in H21.
  discriminate.
  Decompose_sepcon H20 h31 h32.
  eapply Lst_app with (h3 := h31).
  eapply Lst_equiv.
  apply H7.
  generalize (H s H3); intro.
  simpl in H28.
  apply Zeq_bool_true; auto.
  reflexivity.
  apply H12.
  exists (eval e6 s).
  Mapsto.
  Disjoint_heap.
  Disjoint_heap.
  Equal_heap.
  
  simpl in IHentail1.
  simpl in IHentail2.
  inversion_clear H3.
  Decompose_sepcon H5 h1 h2.
  generalize (IHentail1 _ _ (conj H4 H5)); intros.
  clear IHentail1.
  generalize (IHentail2 _ _ H7); intros.
  clear IHentail2.
  inversion_clear H9.
  split; auto.
  Decompose_sepcon H11 h11 h12.
  inversion_clear H7.
  Decompose_sepcon H15 h11' h12'.
  rewrite H6.
  rewrite H12.
  Compose_sepcon h11 (h12 +++ h2); auto.
  inversion_clear H18.
  generalize (H1 s H4); intros.
  unfold eval_pi in H18; Omega_exprb.
  Decompose_sepcon H23 h31 h32.  
  eapply Lst_app with (h3 := h31).
  eapply Lst_equiv.
  apply H8.
  generalize (H s H4); intros.
  unfold eval_pi in H26; Omega_exprb.
  intuition.
  apply H14.
  exists (eval e6 s).
  Mapsto.
  Disjoint_heap.
  Disjoint_heap.
  Equal_heap. 

  red in IHentail; simpl in IHentail.
  inversion_clear H2.
  Decompose_sepcon H4 h1 h2.
  generalize (IHentail _ _ (conj H3 H4)); intros.
  inversion_clear H6.
  split; auto.
  Decompose_sepcon H9 h11 h12.
  Compose_sepcon h11 (h12 +++ h2); auto.
  eapply Lst_app'.
  eapply Lst_equiv.
  apply H7.
  generalize (H s H3); intros.
  unfold eval_pi in H11.
  Omega_exprb.
  intuition.
  apply H12.
  Disjoint_heap.
  Equal_heap.
  generalize (H0 s H3); intros.
  unfold eval_pi in H11; Omega_exprb.

  red in IHentail; simpl in IHentail.
  inversion_clear H3.
  Decompose_sepcon H5 h1 h2.
  generalize (IHentail s h1 (conj H4 H5)); intros.
  inversion_clear H8.
  Decompose_sepcon H11 h11 h12.
  Decompose_sepcon H14 h121 h122.
  inversion_clear H16.
  split; auto.
  Compose_sepcon h11 (h12 +++ h2).
  auto.
  eapply Lst_suiv with (h1 := (h2 +++ h121)) (h2 := h122) (e4 := (int_e x)).
  Disjoint_heap.
  Equal_heap.
  generalize (H0 s H4); generalize (H s H4); intros.
  unfold eval_pi in H16; unfold eval_pi in H19.
  Omega_exprb.
  generalize (H1 s H4); generalize (H s H4); intros.
  unfold eval_pi in H16; unfold eval_pi in H19.
  Omega_exprb.
  generalize (H s H4); generalize (H s H4); intros.
  unfold eval_pi in H16; unfold eval_pi in H19.
  Omega_exprb.
  Compose_sepcon h2 h121.
  Mapsto.
  generalize (H s H4); intros.
  unfold eval_pi in H16.
  Omega_exprb.
  Mapsto.
  generalize (H s H4); intros.
  unfold eval_pi in H16.
  Omega_exprb.
  auto.

  red in IHentail; simpl in IHentail.
  inversion_clear H2.
  Decompose_sepcon H4 h1 h2.
  generalize (IHentail s h1 (conj H3 H4)); intro X; inversion_clear X.
  split.
  auto.
  Compose_sepcon h1 h2.
  auto.
  generalize (H s H3); intros.
  generalize (H0 s H3); intros.
  unfold eval_pi in H10.
  unfold eval_pi in H11.  
  split.
  Mapsto.
  Omega_exprb.

  red in IHentail; simpl in IHentail.
  inversion_clear H1.
  Decompose_sepcon H3 h1 h2.
  generalize (IHentail s h1 (conj H2 H3)); intro X; inversion_clear X.
  split.
  auto.
  Compose_sepcon h1 h2.
  auto.
  generalize (H s H2); intros.
  unfold eval_pi in H9.
  split.
  exists (eval e2 s).
  Mapsto.
  Omega_exprb.

  red in IHentail; simpl in IHentail.
  inversion_clear H1.
  Decompose_sepcon H3 h1 h2.
  generalize (IHentail s h1 (conj H2 H3)); intro X; inversion_clear X.
  split.
  auto.
  Compose_sepcon h1 h2.
  auto.
  generalize (H s H2); intros.
  inversion_clear H5.
  unfold eval_pi in H9.
  split.
  exists x.
  Mapsto.
  Omega_exprb.

  red in IHentail; simpl in IHentail.
  apply IHentail.
  inversion_clear H0.
  split.
  rewrite H1.
  simpl.
  Decompose_sepcon H2 h1 h2.
  Decompose_sepcon H5 h21 h22.
  rewrite (Zeq_bool_false'').
  auto.
  eapply singl_disjoint_neq.
  apply H7.
  apply H5.
  Disjoint_heap.
  auto.

  red in IHentail; simpl in IHentail.
  apply IHentail.
  inversion_clear H0.
  split.
  rewrite H1.
  simpl.
  Decompose_sepcon H2 h1 h2.
  Decompose_sepcon H5 h21 h22.
  inversion_clear H5.
  rewrite (Zeq_bool_false'').
  auto.
  eapply singl_disjoint_neq.
  apply H7.
  apply H8.
  Disjoint_heap.
  auto.

  red in IHentail; simpl in IHentail.
  apply IHentail.
  inversion_clear H0.
  split.
  rewrite H1.
  simpl.
  Decompose_sepcon H2 h1 h2.
  Decompose_sepcon H5 h21 h22.
  inversion_clear H7.
  inversion_clear H5.
  rewrite (Zeq_bool_false'').
  auto.
  eapply singl_disjoint_neq.
  apply H8.
  apply H7.
  Disjoint_heap.
  auto.

  red in IHentail; simpl in IHentail.
  apply IHentail.
  inversion_clear H1.
  split.
  rewrite H2.
  simpl.
  Decompose_sepcon H3 h1 h2.
  Decompose_sepcon H6 h21 h22.
  inversion_clear H8.
  generalize (H s H2); intros.
  unfold eval_pi in H8.
  destruct H6; try Omega_exprb.
  rewrite (Zeq_bool_false'').
  auto.
  Decompose_sepcon H15 h31 h32.
  eapply singl_disjoint_neq.
  apply H17.
  apply H9.
  Disjoint_heap.
  auto.

  red in IHentail; simpl in IHentail.
  apply IHentail.
  inversion_clear H1.
  split.
  rewrite H2.
  simpl.
  Decompose_sepcon H3 h1 h2.
  Decompose_sepcon H6 h21 h22.
  generalize (H s H2); intros.
  unfold eval_pi in H9.
  destruct H6; try Omega_exprb.
  rewrite (Zeq_bool_false'').
  auto.
  Decompose_sepcon H15 h31 h32.
  eapply singl_disjoint_neq.
  apply H17.
  apply H8.
  Disjoint_heap.
  auto.

  red in IHentail; simpl in IHentail.
  apply IHentail.
  inversion_clear H2.
  split.
  rewrite H3.
  simpl.
  Decompose_sepcon H4 h1 h2.
  Decompose_sepcon H7 h21 h22.
  generalize (H s H3); intros.
  generalize (H0 s H3); intros.
  unfold eval_pi in H11.
  unfold eval_pi in H9.
  destruct H7; try Omega_exprb.
  destruct H10; try Omega_exprb.
  repeat rewrite Zeq_bool_false''.
  auto.
  Decompose_sepcon H22 h61 h62.
  Decompose_sepcon H16 h31 h32.
  eapply singl_disjoint_neq.
  apply H26.
  apply H24.
  Disjoint_heap.
  auto.

  red in IHentail; simpl in IHentail.
  apply IHentail.
  inversion_clear H0.
  split; auto.
  Decompose_sepcon H2 h1 h2.
  rewrite H1; simpl.
  rewrite (proj2 (Zeq_bool_false (eval e1 s) 0) H6).
  auto.

  red in IHentail; simpl in IHentail.
  apply IHentail.
  inversion_clear H0.
  split; auto.
  Decompose_sepcon H2 h1 h2.
  rewrite H1; simpl.
  rewrite (proj2 (Zeq_bool_false (eval e1 s) 0) H6).
  auto.

  red in IHentail; simpl in IHentail.
  apply IHentail.
  inversion_clear H1.
  split; auto.
  Decompose_sepcon H3 h1 h2.
  rewrite H2; simpl.
  generalize (H _ H2); intros.
  unfold eval_pi in H5.
  inversion_clear H6.
  simpl in H5.
  rewrite H7; auto.
  rewrite (proj2 (Zeq_bool_false (eval e1 s) 0) H10).
  auto.  

  simpl in IHentail1.
  simpl in IHentail2.
  inversion_clear H1.
  Decompose_sepcon H3 h1 h2.
  generalize (IHentail1 _ _ (conj H2 H3)); 
    generalize (IHentail2 _ _ (conj H2 H6)); intros.
  inversion_clear H5; inversion_clear H7.
  split; auto.
  Compose_sepcon h1 h2; auto.

  simpl in IHentail1.
  simpl in IHentail2.
  assert (Zeq_bool (eval e1 s) (eval e2 s) = true \/ Zeq_bool (eval e1 s) (eval e2 s) = false).
  destruct (Zeq_bool (eval e1 s) (eval e2 s)); auto.
  inversion_clear H2.
  apply IHentail1.
  inversion_clear H1.
  split; auto.
  eapply andb_true_intro.
  split; auto.
  inversion_clear H1.
  apply IHentail2.
  split; auto.
  eapply andb_true_intro.
  split; auto.
  rewrite H3; auto.
Qed.

Lemma entail_to_Sigma_impl : forall sig1 sig2,
  entail (true_b, sig1) (true_b, sig2) ->
  Sigma_interp sig1 ==> Sigma_interp sig2.
Proof.
  intros.
  generalize (entail_soundness _ _ H); intros.
  red in H0; simpl in H0.
  red; intros.
  generalize (H0 _ _ (conj (refl_equal _ ) H1)); intros.
  tauto.
Qed.  

(* tactics to prove a entail goal *)

(* Tactic that turn the left/right hand side of entailment and that add an empty is there is only one subheap*)
Ltac Entail_turnl :=
  match goal with
    | |- entail (?Pi, cell ?e) ?L => eapply entail_empintrol; eapply entail_coml; repeat eapply entail_assocl
    | |- entail (?Pi, singl ?e1 ?e2) ?L => eapply entail_empintrol; eapply entail_coml; repeat eapply entail_assocl
    | |- entail (?Pi, lst ?e1 ?e2) ?L => eapply entail_empintrol; eapply entail_coml; repeat eapply entail_assocl
    | |- entail (?Pi, star ?e1 ?e2) ?L => eapply entail_coml; repeat eapply entail_assocl
    | _ => eapply entail_empintrol; eapply entail_coml; repeat eapply entail_assocl
  end.

Ltac Entail_turnr :=
  match goal with
    | |- entail ?L (?Pi, cell ?e) => eapply entail_empintror; eapply entail_comr; repeat eapply entail_assocr
    | |- entail ?L (?Pi, singl ?e1 ?e2) => eapply entail_empintror; eapply entail_comr; repeat eapply entail_assocr
    | |- entail ?L (?Pi, lst ?e1 ?e2) => eapply entail_empintror; eapply entail_comr; repeat eapply entail_assocr
    | |- entail ?L (?Pi, star ?e1 ?e2) => eapply entail_comr; repeat eapply entail_assocr
    | _ => eapply entail_empintror; eapply entail_comr; repeat eapply entail_assocr
  end.

(* Eliminate left most subheap from lhs and rhs *)

Ltac Elim_subheap := repeat eapply entail_assocl; repeat eapply entail_assocr;
  match goal with 
      
    | |- entail (?pi1, star ?sig1 (singl ?e1 ?e2)) (?pi2, star ?sig2 (singl ?e3 ?e4)) => 
      (eapply entail_star_elim; [unfold eval_pi; Omega_exprb | unfold eval_pi; Omega_exprb | idtac])
      
    | |- entail (?pi1, star ?sig1 (singl ?e1 ?e2)) (?pi2, star ?sig2 (cell ?e3)) => 
      (eapply entail_star_elim'; [unfold eval_pi;  Omega_exprb | idtac])
      
    | |- entail (?pi1, star ?sig1 (cell ?e1)) (?pi2, star ?sig2 (cell ?e3)) => 
      (eapply entail_star_elim''; [unfold eval_pi;  Omega_exprb | idtac])

    | |- entail (?pi1, star ?sig1 (lst ?e1 ?e2)) (?pi2, star ?sig2 (lst ?e3 ?e4)) => 
      ((eapply entail_lstsamelst; [unfold eval_pi; Omega_exprb | unfold eval_pi; Omega_exprb | idtac]) || (eapply entail_lstelim'';[unfold eval_pi; Omega_exprb | unfold eval_pi; Omega_exprb | idtac]))

    | |- entail (?pi1, star ?sig1 (singl ?e1 ?e2)) (?pi2, star ?sig2 (lst ?e3 ?e4)) => 
      (eapply entail_lstelim'''; [unfold eval_pi; Omega_exprb | unfold eval_pi; Omega_exprb | unfold eval_pi; Omega_exprb | idtac])

    | |- entail (?pi1, star ?sig1 ?s) (?pi2, star ?sig2 ?s) => 
      eapply entail_star_elim_star

  end.

(* Prove simple goal (= that not need subheap elimination) *)

Ltac Entail_arith_impl :=
  match goal with
    | |- entail (?pi, ?sig) (?pi, ?sig) => 
      eapply entail_id
    | |- entail (?pi1, emp) (?pi2, emp) => eapply entail_tauto; [unfold eval_pi; intros; Omega_exprb]
    | |- entail (?pi1, emp) (?pi2, emp) => eapply entail_incons; [unfold eval_pi; intros; Omega_exprb]
  end.

(* elimine every empty subheap *)

Ltac Entail_elim_emp :=
  match goal with
    | |- entail (?pi1, star ?sig1 emp) (?pi2, ?sig2) => eapply entail_epseliml; Entail_elim_emp
    | |- entail (?pi1, ?sig1) (?pi2, star ?sig2 emp) => eapply entail_epselimr; Entail_elim_emp
    | |- _ => idtac
  end.

(* add location not null constraints *)

Ltac Entail_not_nul_constraint :=
  match goal with
    | |- entail (?pi1, star ?sig1 (cell ?e)) (?pi2, ?sig2) => 
      eapply entail_cell_not_null; idtac
    | |- entail (?pi1, star ?sig1 (singl ?e1 ? e2)) (?pi2, ?sig2) => 
      eapply entail_singl_not_null; idtac
    | |- entail (?pi1, star ?sig1 (lst ?e1 ? e2)) (?pi2, ?sig2) => 
      eapply entail_lst_not_null; [unfold eval_pi; Omega_exprb | idtac]
    | |- _ => idtac
  end.

(* compute the number of subheap *)

Ltac Entail_count_subheap sig :=
  match sig with
    | star ?sig1 ?sig2 =>
      let x := Entail_count_subheap sig1 in (
        let y := Entail_count_subheap sig2 in (
          constr:(x + y)
        )
      )
    | _ => 
      constr:(1)
  end.

(* tactic for debugging *)

Ltac Printt x := assert (x = x).

(* Turn the rhs at most m time until an elimination could be performed *) 

Ltac Entail_elim_right n m :=
  let y := (constr:(nat_gt n m)) in (
    match (eval compute in y) with
      | true => idtac
      | false =>
        Entail_turnr; (Elim_subheap || (
        let x := (constr:(S n)) in (
          Entail_elim_right x m
        )
        )
        )
    end
  ).

(* try to solve the goal or try to eliminate the left most subheap of lhs *)

Ltac Entail_elim_left := Entail_not_nul_constraint;
  match goal with
    | |- entail (?pi1, ?sig1) (?pi2, ?sig2) =>
      Entail_elim_emp; Entail_arith_impl
    | |- entail (?pi1, ?sig1) (?pi2, ?sig2) =>
      let x := Entail_count_subheap sig2 in (
        let vx := eval compute in x in (
          Entail_elim_right 0 vx
        )
      ); Entail_turnl
  end.

Ltac Entail := repeat Entail_elim_left.
  


(*
 Exemple in the PPL 2007 draft 
 (due to name collision between example variable and next lemmas it is
 commented. You can try it by decommenting, but be sure to recomment
 it to proceed the file typing)*)

(*

Definition nil : expr := nat_e 0.
Definition e : expr := var_e 0.
Definition e' : expr := var_e 1.
Definition e'' : expr := var_e 2.


Goal
entail
(true_b,
star (lst e e') (
star (singl e' e'') (
star (cell (e' +e (nat_e 1))) (
lst e'' (nat_e 0)
)))) 
(true_b, lst e (nat_e 0)).
unfold e; unfold e'; unfold e''; unfold nil.
Entail.
Qed.

*)

(*
Definition null : expr := nat_e 0.
Definition v1 : expr := var_e 4.
Definition v2 : expr := var_e 5.
Definition x1 : expr := var_e 0.
Definition x2 : expr := var_e 1.
Definition x3 : expr := var_e 2.
Definition x4 : expr := var_e 3.
Definition x5 : expr := var_e 4.
Definition x6 : expr := var_e 5.

Definition P := (
  (x3 =/= null) &&& (x5 =/= null) &&& (x6 == null) &&& (x3 =/= x5),
  (star
    (lst x1 x3)
    (star 
      (singl x3 x5)
      (star 
        (cell (x3 +e (nat_e 1)))
        (lst x5 x6)
      ) 
    )    
  )
).

Definition Q' := ( true_b, star (lst x1 x5) (lst x5 x6) ).

Definition Q := ( true_b, (lst x1 x6) ).

Ltac Print h :=
  let y := (eval compute in h) in (
    assert (y = y); auto
  ).

Ltac Nb_sig_elt sig :=
  match sig with
    | singl ?e1 ?e2 =>
      constr:1
    | cell ?e1 =>
      constr:1
    | emp =>
      constr:1
    | star ?sig1 ?sig2 =>
      let x := (Nb_sig_elt sig1) in (
        let y := (Nb_sig_elt sig2) in (
          constr:(x + y)
        )
      )
    | lst ?e1 ?e2 =>
      constr:1
  end.

Ltac Nb_sig_elt_entail_right :=
  match goal with
    | |- entail (?pi1,?sig1) (?pi2,?sig2) =>
      Nb_sig_elt sig2
  end.

Ltac Nb_sig_elt_entail_left :=
  match goal with
    | |- entail (?pi1,?sig1) (?pi2,?sig2) =>
      Nb_sig_elt sig1
  end. 

Goal (assrt_interp P) ==> (assrt_interp Q).
  apply entail_soundness.
  unfold P; unfold Q; unfold x1; unfold x2; unfold x3; unfold x4 ; unfold x5; unfold x6; unfold null.  
  Entail.
Qed.

Goal   (assrt_interp P) ==> (assrt_interp Q').
  apply entail_soundness.
  unfold P; unfold Q'; unfold x1; unfold x2; unfold x3; unfold x4 ; unfold x5; unfold x6; unfold null.

  entail_turnl.
  entail_turnr.
  eapply entail_lstelim'_v2.
  intros; Omega_exprb.
  entail_turnl.
  entail_turnl.
  eapply entail_star_elim_lst.
  eapply entail_id.
  intros; Omega_exprb.

  entail_turnr.
  entail_turnl.
  entail_turnl.
  entail_turnl.
  eapply entail_lstsamelst.
  intros; Omega_exprb.
  intros; Omega_exprb.

  entail_turnr.
  entail_turnl.  
  eapply entail_lstelim'''.
  intros; Omega_exprb.
  intros; Omega_exprb.
  intros; Omega_exprb.

  entail_turnr.
  entail_turnl.  
  entail_turnr.
  eapply entail_lstnilelimr.
  intros; Omega_exprb.

  entail_resolve.
  entail_resolve.
Qed.
*)  


(****************************)

(* load the decision procedure for expr_b *)
Require Import expr_b_dp.

Fixpoint remove_empty_heap  (pi : Pi) (sig : Sigma) {struct sig} : Sigma :=
  match sig with
    | star sig1 sig2 =>
      match remove_empty_heap pi sig1 with
        | emp => remove_empty_heap pi sig2
        | sig1' => match remove_empty_heap pi sig2 with
                   | emp => sig1'
                   | sig2' => star sig1' sig2'
                 end
      end
    | lst e1 e2 => if expr_b_dp (pi =b> (e1 == e2)) then emp else sig
    | _ => sig
  end.

Lemma remove_empty_heap_correct : forall sig pi s,
  s |b= pi ->  
  forall h,
  (Sigma_interp (remove_empty_heap pi sig) s h -> Sigma_interp sig s h).
Proof.
  induction sig; simpl; intros; auto.
  generalize (IHsig1 pi); clear IHsig1; intro IHsig1.
  generalize (IHsig2 pi); clear IHsig2; intro IHsig2.
  destruct (remove_empty_heap pi sig1); destruct (remove_empty_heap pi sig2); simpl in H0; simpl; simpl in IHsig1; simpl in IHsig2;
    (try (
      (Decompose_sepcon H0 h1 h2; Compose_sepcon h1 h2; [apply (IHsig1 _ H); tauto | apply (IHsig2 _ H); tauto])
      || (Compose_sepcon h heap.emp; [apply (IHsig1 _ H); tauto | apply (IHsig2 _ H); simpl; red; tauto])
        || (Compose_sepcon heap.emp h; [apply (IHsig1 _ H); simpl; red; tauto | apply (IHsig2 _ H); tauto])
          || (red in H0; Compose_sepcon heap.emp heap.emp; [apply (IHsig1 _ H); simpl; red; tauto | apply (IHsig2 _ H); simpl; red; tauto])
      )).
  generalize (expr_b_dp_correct (pi =b> e == e0)); intros.  
  destruct (expr_b_dp (pi =b> e == e0)); simpl in H.
  generalize (H1 (refl_equal _) s); intros.
  apply Lst_end.
  
  Omega_exprb.
  auto.
  auto.
Qed.

Lemma remove_empty_heap_correct' : forall sig pi s,
  s |b= pi ->  
  forall h,
  (Sigma_interp sig s h -> Sigma_interp (remove_empty_heap pi sig) s h).
Proof.
  induction sig; simpl; intros; auto.
  generalize (IHsig1 pi); clear IHsig1; intro IHsig1.
  generalize (IHsig2 pi); clear IHsig2; intro IHsig2.
  destruct (remove_empty_heap pi sig1); destruct (remove_empty_heap pi sig2); simpl in H0; simpl;
    (try (
      (Decompose_sepcon H0 h1 h2; Compose_sepcon h1 h2; [apply IHsig1; tauto | apply IHsig2; tauto])
      || (Decompose_sepcon H0 h1 h2; generalize (IHsig2 _ H  _ H4); intros; simpl in H3; red in H3; subst h2; assert (h = h1); [Equal_heap | subst h1; apply (IHsig1 _ H); tauto])
      || (Decompose_sepcon H0 h1 h2; generalize (IHsig1 _ H _ H1); intros; simpl in H3; red in H3; subst h1; assert (h = h2); [Equal_heap | subst h2; apply IHsig2; tauto])
    )).
  generalize (expr_b_dp_correct (pi =b> e == e0)); intros.  
  destruct (expr_b_dp (pi =b> e == e0)).
  generalize (H1 (refl_equal _) s); intros.
  destruct H0.
  simpl; red in H3; auto.
  Omega_exprb.
  auto.
Qed.

(* returns true if <env,sig> contains (cell e), (singl e _), or (lst e _) =/= emp *)
Fixpoint cell_in_sigma (pi : Pi) (sig : Sigma) (e : expr) {struct sig} : bool :=
  match sig with
    | singl e1 e2 => expr_b_dp (pi =b> (e1 == e))
    | cell e1 => expr_b_dp (pi =b> (e1 == e))
    | lst e1 e2 => andb 
      (expr_b_dp (pi =b> (e1 == e))) 
      (expr_b_dp (pi =b> (e1 =/= e2)))
    | star s1 s2 => orb (cell_in_sigma pi s1 e ) (cell_in_sigma pi s2 e)
    | _ => false
  end.

Lemma cell_in_sigma_correct: forall sig e pi,
  cell_in_sigma pi sig e = true ->
  forall s h,
    s |b= pi ->
    Sigma_interp sig s h -> ((Sigma_interp (cell e)) ** TT) s h.
  induction sig; simpl; intros; try discriminate.

  generalize (expr_b_dp_correct _ H s); intros.
  Compose_sepcon h heap.emp.
  inversion_clear H1.
  split.
  exists (eval e0 s).
  Mapsto.
  red; intros; eapply H4.
  cutrewrite (eval e s = eval e1 s).
  Omega_exprb.
  Omega_exprb.
  red; auto.

  generalize (expr_b_dp_correct _ H s); intros.
  Compose_sepcon h heap.emp.
  inversion_clear H1.
  inversion_clear H3.
  split.
  exists x; Mapsto.
  cutrewrite (eval e0 s = eval e s).
  Omega_exprb.
  symmetry.
  Omega_exprb.
  red; auto.

  generalize (IHsig1 e pi); generalize (IHsig2 e pi); clear IHsig1 IHsig2; intros.
  destruct (cell_in_sigma pi sig1 e); destruct (cell_in_sigma pi sig2 e); simpl in H; try discriminate.
  Decompose_sepcon H1 h1 h2.
  generalize (H2 (refl_equal _) _ _ H0 H7); clear H2; intros.
  generalize (H3 (refl_equal _) _ _ H0 H4); clear H3; intros.
  Decompose_sepcon H2 h21 h22.
  simpl in H6.
  inversion_clear H6.
  Compose_sepcon h21 (h1 +++ h22).
  split; auto.
  red; auto.
  Decompose_sepcon H1 h1 h2.
  generalize (H3 (refl_equal _) _ _ H0 H4); clear H3; intros.
  Decompose_sepcon H3 h11 h12.
  simpl in H6; inversion_clear H6.
  Compose_sepcon h11 (h12 +++ h2).
  split; auto.
  red; auto.
  Decompose_sepcon H1 h1 h2.
  generalize (H2 (refl_equal _) _ _ H0 H7); clear H2; intros.
  Decompose_sepcon H2 h21 h22.
  simpl in H6; inversion_clear H6.
  Compose_sepcon h21 (h22 +++ h1).
  split; auto.
  red; auto.

  generalize (andb_prop _ _ H); intro X; inversion_clear X; clear H.  
  generalize (expr_b_dp_correct _ H3 s); clear H3; intros.
  generalize (expr_b_dp_correct _ H2 s); clear H2; intros.
  destruct H1.
  Omega_exprb.
  Decompose_sepcon H7 h11 h12.
  Compose_sepcon h11 (h12 +++ h2).
  split; auto.
  exists (eval e2 s); Mapsto.
  cutrewrite (eval e1 s = eval e0 s).
  Omega_exprb.
  symmetry.
  Omega_exprb.
  red; auto.
Qed.  

Opaque remove_empty_heap.

(* returns true if two sigmas are the two same singl, cell ou lst *)
Definition sigma_eq (pi : Pi) (sig1 sig2 : Sigma)  : bool :=
  match (sig1, sig2) with
    | (emp, emp) => true
    | (singl e1 e2, singl e3 e4) => andb (expr_b_dp (pi =b> (e1 == e3))) (expr_b_dp (pi =b> (e2 == e4)))
    | (singl e1 e2, cell e3) => expr_b_dp (pi =b> (e1 == e3))
    | (cell e1, cell e3) => expr_b_dp (pi =b> (e1 == e3)) 
    | (lst e1 e2, lst e3 e4) => andb (expr_b_dp (pi =b> (e1 == e3))) (expr_b_dp (pi =b> (e2 == e4)))
    | (_, _) => false
  end.

Lemma sigma_eq_correct: forall sig1 sig2 pi,
  sigma_eq pi sig1 sig2 = true ->
  (forall s h,
    s |b= pi ->
    (Sigma_interp sig1 s h -> Sigma_interp sig2 s h)
  ).
  destruct sig1; destruct sig2; simpl; intros; try discriminate.
  unfold sigma_eq in H.
  generalize (andb_prop _ _ H); intro X; inversion_clear X; clear H.
  generalize (expr_b_dp_correct _ H2 s); intros.
  generalize (expr_b_dp_correct _ H3 s); intros.
  inversion_clear H1.
  split.
  Mapsto.
  cutrewrite (eval e1 s = eval e s).
  auto.
  symmetry.
  Omega_exprb.
  inversion_clear H1.
  split; auto.
  exists (eval e0 s).
  unfold sigma_eq in H.
  generalize (expr_b_dp_correct _ H s); intros.
  Mapsto.
  generalize (expr_b_dp_correct _ H s); intros.
  cutrewrite (eval e1 s = eval e s).
  Omega_exprb.
  symmetry.
  Omega_exprb.    
  inversion_clear H1.
  inversion_clear H2.
  generalize (expr_b_dp_correct _ H s); intros.
  split.
  exists x.
  unfold sigma_eq in H.  
  Mapsto.
  cutrewrite (eval e0 s = eval e s).
  Omega_exprb.
  symmetry.
  Omega_exprb.      
  auto.
  unfold sigma_eq in H.
  generalize (andb_prop _ _ H); intro X; inversion_clear X; clear H.
  generalize (expr_b_dp_correct _ H2 s); intros.
  generalize (expr_b_dp_correct _ H3 s); intros.
  eapply Lst_equiv.
  apply H1.
  Omega_exprb.
  Omega_exprb.
Qed.


(* remove the cell sig of the heap (sig ** sig1) from the heap sig2 *)
Fixpoint elim_common_cell (pi : Pi) (sig1 remainder sig2 : Sigma)  {struct sig2} : option (Sigma * Sigma) :=
  match sig2 with
    | star sig21 sig22 =>
      match elim_common_cell pi sig1 remainder sig21 with
        | None => 
          match elim_common_cell pi sig1 remainder sig22 with
            | None => None
            | Some (sig1', sig2') => Some (sig1', remove_empty_heap pi (star sig21 sig2'))
          end
        | Some (sig1', sig2') => Some (sig1', remove_empty_heap pi (star sig2' sig22))
      end
    | _ => 
      if sigma_eq  pi sig1 sig2 then Some (emp, emp) else 
        match (sig1, sig2) with
          | (lst e11 e12, lst e21 e22) => 
            if andb 
              (expr_b_dp (pi =b> (e11 == e21))) 
              (orb  
                (expr_b_dp (pi =b> (e22 == nat_e 0)))
                (cell_in_sigma pi remainder e22) (* cell l22 is contained in remainder *)) 
              then Some (emp, lst e12 e22) (* sig1 is the prefix-list of sig2 *)
              else None
          | (singl e1 e2, lst e3 e4) =>
            if andb (expr_b_dp (pi =b> (e1 == e3))) 
              (andb (expr_b_dp (pi =b> (e1 =/= e4))) 
                (expr_b_dp (pi =b> (e1 =/= nat_e 0)))) 
              then Some (emp, (star (cell (e1 +e nat_e 1)) (lst e2 e4))) 
                (* sig1 is the leading node of list sig2 *)
              else None
          | (emp, lst e3 e4) => 
            if expr_b_dp (pi =b> (e3 == e4)) 
              then Some (emp, emp) 
              else Some (emp, sig2)
          | (emp, _) => Some (emp, sig2)
          | _ => None
        end
  end.

Lemma elim_common_cell_mp : forall sig2 sig1 remainder pi sig1' sig2',
  elim_common_cell pi sig1 remainder sig2 = Some (sig1', sig2') ->
  (Sigma_interp sig1 ==> (Sigma_interp sig1' -* Sigma_interp sig1) ** Sigma_interp sig1').
  induction sig2; simpl; intros.

(**)

  destruct (sigma_eq pi sig1 (singl e e0)).
  injection H; intros; subst sig1' sig2'.
  red; intros.
  Compose_sepcon h heap.emp.
  Intro_sepimp h' h0'.
  simpl in H2; red in H2; subst h'.
  cutrewrite (h0' = h); [auto | Equal_heap].
  simpl; red; auto.
  destruct sig1; try discriminate.
  injection H; intros; subst sig1' sig2'.
  red; simpl; intros.
  Compose_sepcon heap.emp heap.emp.
  Intro_sepimp h' h''.
  red in H2; simpl in H2; subst h'.
  cutrewrite (h'' = heap.emp); [auto | Equal_heap].
  red; auto.
  red; auto.

(**)

  destruct (sigma_eq pi sig1 (cell e)).
  injection H; intros; subst sig1' sig2'.
  red; intros.
  Compose_sepcon h heap.emp.
  Intro_sepimp h' h0'.
  simpl in H2; red in H2; subst h'.
  cutrewrite (h0' = h); [auto | Equal_heap].
  simpl; red; auto.
  destruct sig1; try discriminate.
  injection H; intros; subst sig1' sig2'.
  red; simpl; intros.
  Compose_sepcon heap.emp heap.emp.
  Intro_sepimp h' h''.
  red in H2; simpl in H2; subst h'.
  cutrewrite (h'' = heap.emp); [auto | Equal_heap].
  red; auto.
  red; auto.

(**) 

  destruct (sigma_eq pi sig1 emp).
  injection H; intros; subst sig1' sig2'.
  red; intros.
  Compose_sepcon h heap.emp.
  Intro_sepimp h' h0'.
  simpl in H2; red in H2; subst h'.
  cutrewrite (h0' = h); [auto | Equal_heap].
  simpl; red; auto.
  destruct sig1; try discriminate.
  injection H; intros; subst sig1' sig2'.
  red; simpl; intros.
  Compose_sepcon heap.emp heap.emp.
  Intro_sepimp h' h''.
  red in H2; simpl in H2; subst h'.
  cutrewrite (h'' = heap.emp); [auto | Equal_heap].
  red; auto.
  red; auto.

  generalize (IHsig2_1 sig1 remainder pi); clear IHsig2_1; intros.
  destruct (elim_common_cell pi sig1 remainder sig2_1).
  clear IHsig2_2.
  destruct p.
  injection H; intros; clear H; subst sig1' sig2'.
  generalize (H0 _ _ (refl_equal _)); clear H0; intros.
  auto.
  
  clear H0.
  
  generalize (IHsig2_2 sig1 remainder pi); clear IHsig2_2; intros.
  destruct (elim_common_cell pi sig1 remainder sig2_2); try discriminate.
  destruct p.
  injection H; intros; clear H; subst sig1' sig2'.
  generalize (H0 _ _ (refl_equal _)); clear H0; intros.
  auto.

(**)

  destruct (sigma_eq pi sig1 (lst e e0)).
  injection H; clear H; intros; subst sig1' sig2'.
  red; simpl; intros.
  Compose_sepcon h heap.emp.
  Intro_sepimp h' h''.
  red in H1; subst h'; cutrewrite (h'' = h); [auto | Equal_heap].
  red; auto.
  
  destruct sig1; try discriminate.
  
  destruct (expr_b_dp (pi =b> e1 == e)); destruct (expr_b_dp (pi =b> e1 =/= e0)); destruct (expr_b_dp (pi =b> e1 =/= nat_e 0)); simpl in H; try discriminate.
  injection H; clear H; intros; subst sig1' sig2'.
  simpl.
  red; intros.
  Compose_sepcon h heap.emp.
  Intro_sepimp h' h''.
  red in H1; subst h'.
  inversion_clear H.
  cutrewrite (h'' = h); [split; [Mapsto | tauto] | Equal_heap].
  red; auto.

  destruct (expr_b_dp (pi =b> e == e0)); simpl in H; try discriminate.
  injection H; clear H; intros; subst sig1' sig2'.
  simpl; red; intros.
  Compose_sepcon h heap.emp.
  Intro_sepimp h' h''.
  red in H1; subst h'.
  red in H; subst h.
  cutrewrite (h'' = heap.emp); [red; auto | Equal_heap].
  red; auto.

  injection H; clear H; intros; subst sig1' sig2'.
  simpl; red; intros.
  Compose_sepcon h heap.emp.
  Intro_sepimp h' h''.
  red in H1; subst h'.
  red in H; subst h.
  cutrewrite (h'' = heap.emp); [red; auto | Equal_heap].
  red; auto.

  destruct (expr_b_dp (pi =b> e1 == e)); simpl in H; try discriminate.
  destruct (expr_b_dp  (pi =b> e0 == nat_e 0)); simpl in H; try discriminate.
  injection H; clear H; intros; subst sig1' sig2'.
  simpl; red; intros.
  Compose_sepcon h heap.emp.
  Intro_sepimp h' h''.
  red in H1; subst h'.
  cutrewrite (h'' = h); [auto | Equal_heap].
  red; auto.
  
  destruct (cell_in_sigma pi remainder e0); simpl in H; try discriminate.
  injection H; clear H; intros; subst sig1' sig2'.
  simpl.
  red; intros.
  Compose_sepcon h heap.emp.
  Intro_sepimp h' h''.
  red in H1; subst h'.
  cutrewrite (h'' = h); [auto | Equal_heap].
  red; auto.
Qed.  

Lemma elim_common_cell_correct : forall sig2 sig1 remainder pi sig1' sig2',
  elim_common_cell pi sig1 remainder sig2 = Some (sig1', sig2') ->
  forall s,
    s |b= pi ->
    forall h1 h2 h3 h,      
      Sigma_interp sig2' s h1 ->
      (Sigma_interp sig1' -* Sigma_interp sig1) s h2 ->
      Sigma_interp remainder s h3 ->
      h = h1 +++ h2 ->
      h1 # h2 ->
      h2 # h3 ->
      Sigma_interp sig2 s h.
Proof.
  induction sig2; simpl; intros.

(**)

  generalize (sigma_eq_correct sig1 (singl e e0) pi); intros.
  destruct (sigma_eq pi sig1 (singl e e0)).
  injection H; intros; subst sig1' sig2'.
  simpl in H7.
  eapply H7; auto.
  eapply H2 with (h' := h1).
  split; [Disjoint_heap | auto].
  Equal_heap.
  clear H7.
  destruct sig1; try discriminate.
  injection H; intros; subst sig1' sig2'.
  simpl in H2; simpl in H1.
  assert (sep.emp s h2).
  apply H2 with (h' := heap.emp); auto.
  split; [Disjoint_heap | red; auto].
  Equal_heap.
  cutrewrite (h = h1).
  auto.
  red in H7; subst h2.
  Equal_heap.

(**)

  generalize (sigma_eq_correct sig1 (cell e) pi); intros.
  destruct (sigma_eq pi sig1 (cell e)).
  injection H; intros; subst sig1' sig2'.
  simpl in H7.
  eapply H7; auto.
  eapply H2 with (h' := h1).
  split; [Disjoint_heap | auto].
  Equal_heap.
  clear H7.
  destruct sig1; try discriminate.
  injection H; intros; subst sig1' sig2'.
  simpl in H2; simpl in H1.
  assert (sep.emp s h2).
  apply H2 with (h' := heap.emp); auto.
  split; [Disjoint_heap | red; auto].
  Equal_heap.
  cutrewrite (h = h1).
  auto.
  red in H7; subst h2.
  Equal_heap.

(**)  

  generalize (sigma_eq_correct sig1 emp pi); intros.
  destruct (sigma_eq pi sig1 emp).
  injection H; intros; subst sig1' sig2'.
  simpl in H7.
  eapply H7; auto.
  eapply H2 with (h' := h1).
  split; [Disjoint_heap | auto].
  Equal_heap.
  clear H7.
  destruct sig1; try discriminate.
  injection H; intros; subst sig1' sig2'.
  simpl in H2; simpl in H1.
  assert (sep.emp s h2).
  apply H2 with (h' := heap.emp); auto.
  split; [Disjoint_heap | red; auto].
  Equal_heap.
  cutrewrite (h = h1).
  auto.
  red in H7; subst h2.
  Equal_heap.

(**)

  generalize (IHsig2_1 sig1 remainder pi); clear IHsig2_1; intros.
  destruct (elim_common_cell pi sig1 remainder sig2_1); try discriminate.
  destruct p.
  injection H; clear H; intros; subst sig1' sig2'.
  assert (Sigma_interp (star s1 sig2_2) s h1).
  eapply remove_empty_heap_correct.
  apply H0.
  auto.
  clear H1.
  simpl in H.
  Decompose_sepcon H h11 h12.
  Compose_sepcon (h11 +++ h2) h12.
  eapply H7.
  intuition.
  auto.
  apply H1.
  apply H2.
  apply H3.
  auto.
  Disjoint_heap.
  Disjoint_heap.
  auto.

  clear H7.

  generalize (IHsig2_2 sig1 remainder pi); clear IHsig2_2; intros.
  destruct (elim_common_cell pi sig1 remainder sig2_2); try discriminate.
  destruct p.
  injection H; clear H; intros; subst sig1' sig2'.
  assert (Sigma_interp (star sig2_1 s1) s h1).
  eapply remove_empty_heap_correct.
  apply H0.
  auto.
  clear H1.
  simpl in H.
  Decompose_sepcon H h11 h12.
  Compose_sepcon h11 (h12 +++ h2).
  eapply H1.
  auto.
  eapply H7.  
  intuition.
  apply H0.
  apply H10.
  apply H2.
  apply H3.
  auto.
  Disjoint_heap.
  Disjoint_heap.

(**)
  
  generalize (sigma_eq_correct sig1 (lst e e0) pi); intros.
  destruct (sigma_eq pi sig1 (lst e e0)).
  injection H; intros; subst sig1' sig2'.
  simpl in H7.
  eapply H7; auto.
  eapply H2 with (h' := h1).
  split; [Disjoint_heap | auto].
  Equal_heap.
  clear H7.
  destruct sig1; try discriminate.

  generalize (expr_b_dp_correct (pi =b> e1 == e)); intros.
  destruct (expr_b_dp (pi =b> e1 == e)); simpl in H; try discriminate.
  generalize (expr_b_dp_correct (pi =b> e1 =/= e0)); intros.
  destruct (expr_b_dp (pi =b> e1 =/= e0)); simpl in H; try discriminate.
  generalize (expr_b_dp_correct (pi =b> e1 =/= nat_e 0)); intros.
  destruct (expr_b_dp (pi =b> e1 =/= nat_e 0)); simpl in H; try discriminate.
  generalize (H7 (refl_equal _) s); generalize (H8 (refl_equal _) s); generalize (H9 (refl_equal _) s); clear H7 H8 H9; intros.
  injection H; clear H; intros; subst sig1' sig2'.
  simpl in H2; simpl in H1.
  Decompose_sepcon H1 h11 h12.
  inversion_clear H11.
  eapply Lst_suiv with (h1 := (h2 +++ h11)) (h2 := h12) (e2 := e2) (e4 := int_e x).
  Disjoint_heap.
  Equal_heap.
  cutrewrite (eval e s = eval e1 s).
  Omega_exprb.
  symmetry; Omega_exprb.
  cutrewrite (eval e s = eval e1 s).
  Omega_exprb.
  symmetry; Omega_exprb.
  simpl.
  cutrewrite (eval e s = eval e1 s).
  Omega_exprb.
  symmetry; Omega_exprb.
  Compose_sepcon h2 h11.
  assert ((e1 |-> e2) s h2).
  assert (h2 # heap.emp /\ sep.emp s heap.emp).
  split; [Disjoint_heap | red; auto].
  assert (h2 = h2 +++ heap.emp).
  Equal_heap.
  apply (proj1  (H2 heap.emp H11 h2 H14)).
  Mapsto.
  Mapsto.
  cutrewrite (eval e s = eval e1 s).
  Omega_exprb.
  symmetry; Omega_exprb.
  auto.

  generalize (expr_b_dp_correct (pi =b> e == e0)); intros.
  destruct (expr_b_dp (pi =b> e == e0)); simpl in H; try discriminate.
  generalize (H7 (refl_equal _) s); clear H7; intros.  
  injection H; clear H; intros; subst sig1' sig2'.
  assert (sep.emp s h2).
  eapply H2 with (h' := heap.emp).
  split; [Disjoint_heap | simpl; red; auto].
  Equal_heap.
  cutrewrite (h = h1); auto.
  eapply Lst_end.
  Omega_exprb.
  auto.
  simpl in H1; red in H1; red in H; subst h1 h2; Equal_heap.
  clear H7.
  injection H; clear H; intros; subst sig1' sig2'.
  assert (sep.emp s h2).
  eapply H2 with (h' := heap.emp).
  split; [Disjoint_heap | simpl; red; auto].
  Equal_heap.
  red in H; subst h2.
  cutrewrite (h = h1); auto.
  Equal_heap.

  generalize (expr_b_dp_correct (pi =b> e1 == e)); intros.
  destruct (expr_b_dp (pi =b> e1 == e)); simpl in H; try discriminate.
  generalize (H7 (refl_equal _) s); clear H7; intros.  
  generalize (expr_b_dp_correct (pi =b> e0 == nat_e 0)); intros.
  destruct (expr_b_dp (pi =b> e0 == nat_e 0)); simpl in H.
  generalize (H8 (refl_equal _) s); clear H8; intros.  
  injection H; clear H; intros; subst sig1' sig2'.
  simpl in H2; simpl in  H1.
  eapply Lst_equiv.
  eapply Lst_app'.
  apply H2 with (h' := heap.emp).
  split; [Disjoint_heap | red; auto].
  intuition.
  eapply H1.
  Disjoint_heap.
  Equal_heap.
  Omega_exprb.
  Omega_exprb.
  auto.
  
  clear H8.

  generalize (cell_in_sigma_correct remainder e0 pi); intros.
  destruct (cell_in_sigma pi remainder e0); try discriminate.
  generalize (H8 (refl_equal _) s); clear H8; intros.  
  injection H; clear H; intros; subst sig1' sig2'.
  simpl in H8; simpl in H2; simpl in H1.
  generalize (H8 _ H0 H3); intros.
  clear H8.
  Decompose_sepcon H h31 h32.
  eapply Lst_equiv.
  eapply Lst_app.
  apply H2 with (h' := heap.emp).
  split; [Disjoint_heap | red; auto].
  intuition.
  eapply H1.
  apply H10.
  Disjoint_heap.
  Disjoint_heap.
  Equal_heap.
  Omega_exprb.
  Omega_exprb.
Qed. 

(* try to match sig1 with sig2, remainder is that part of sig1 that is left aside *)
Fixpoint elim_common_subheap (pi : Pi) (sig1 sig2 remainder : Sigma) {struct sig1} : option (Sigma * Sigma) :=
  match sig1 with
    | star sig11 sig12 =>
      match elim_common_subheap pi sig11 sig2 (star sig12 remainder) with
        | None => None
        | Some (sig11', sig12') => Some (remove_empty_heap pi (star sig11' sig12), sig12')
      end
    | _ => elim_common_cell pi sig1 remainder sig2
  end.

Lemma elim_common_subheap_correct: forall sig1 sig2 remainder pi sig1' sig2',
  elim_common_subheap pi sig1 sig2 remainder = Some (sig1', sig2') ->
  forall s,
    s |b= pi ->    
    (forall h, Sigma_interp (star remainder sig1') s h -> Sigma_interp sig2' s h) ->
    (forall h, Sigma_interp (star sig1 remainder) s h -> Sigma_interp sig2 s h).
  induction sig1; simpl; intros.

(**)

  generalize (elim_common_cell_mp sig2 _ remainder pi sig1' sig2' H); intros.
  Decompose_sepcon H2 h1 h2.
  generalize (H3 _ _ (conj H6 H8)); clear H3 H6 H8; intros.
  Decompose_sepcon H3 h11 h12.
  eapply (elim_common_cell_correct sig2 _ remainder pi sig1' sig2' H _ H0); intros. 
  eapply H1.
  assert ((Sigma_interp remainder ** Sigma_interp sig1') s (h2 +++ h12)).
  Compose_sepcon h2 h12; auto.
  apply H8.
  apply H4.
  apply H7.
  Equal_heap.
  Disjoint_heap.
  Disjoint_heap. 

(**)

  Decompose_sepcon H2 h1 h2.
  
  generalize (elim_common_cell_mp sig2 _ remainder pi sig1' sig2' H); intros.
  simpl in H3; red in H3.
  generalize (H3 _ _ (conj H5 H7)); clear H5 H7; intros.
  Decompose_sepcon H5 h11 h12.
  eapply (elim_common_cell_correct sig2 _ remainder pi sig1' sig2' H _ H0); intros. 
  eapply H1.
  assert ((Sigma_interp remainder ** Sigma_interp sig1') s (h2 +++ h12)).
  Compose_sepcon h2 h12; auto.
  apply H9.
  apply H7.
  apply H6.
  Equal_heap.
  Disjoint_heap.
  Disjoint_heap. 

(**)

  Decompose_sepcon H2 h1 h2.
  
  generalize (elim_common_cell_mp sig2 _ remainder pi sig1' sig2' H); intros.
  simpl in H5; red in H5.
  generalize (H5 _ _ H3); clear H5; intros.
  Decompose_sepcon H5 h11 h12.

  eapply (elim_common_cell_correct sig2 _ remainder pi sig1' sig2' H _ H0); intros. 
  eapply H1.
  assert ((Sigma_interp remainder ** Sigma_interp sig1') s (h2 +++ h12)).
  Compose_sepcon h2 h12; auto.
  apply H9.
  apply H7.
  apply H6.
  Equal_heap.
  Disjoint_heap.
  Disjoint_heap. 

(**)

  generalize (IHsig1_1 sig2 (star sig1_2 remainder) pi); clear IHsig1_1; intros.
  destruct (elim_common_subheap pi sig1_1 sig2 (star sig1_2 remainder)); try discriminate.
  destruct p; injection H; intros; subst sig1' sig2'; clear H.
  apply (H3 _ _ (refl_equal _) _ H0); clear H3.
  simpl.
  intros.
  eapply H1.
  Decompose_sepcon H h01 h02.
  Decompose_sepcon H3 h011 h012.
  Compose_sepcon h012 (h011 +++ h02); auto.
  eapply remove_empty_heap_correct'.
  apply H0.
  simpl.
  Compose_sepcon h02 h011; auto.
  Decompose_sepcon H2 h1 h2.
  simpl.
  Decompose_sepcon H2 h11 h12.
  Compose_sepcon h11 (h12 +++ h2); auto.
  Compose_sepcon h12 h2; auto.

(**)

  generalize (elim_common_cell_mp sig2 _ remainder pi sig1' sig2' H); intros.
  simpl in H3; red in H3.
  
  Decompose_sepcon H2 h1 h2.
  generalize (H3 _ _ H4); clear H4 H3; intros.
  Decompose_sepcon H3 h11 h12.
  
  eapply (elim_common_cell_correct sig2 _ remainder pi sig1' sig2' H _ H0 ); intros.
  assert (Sigma_interp sig2' s (h2 +++ h12)).
  eapply H1.
  Compose_sepcon h2 h12; auto.
  apply H8.
  simpl; apply H4.
  apply H7.
  Equal_heap.
  Disjoint_heap.
  Disjoint_heap.
Qed.

Fixpoint star_assoc_left (sig1 sig2: Sigma) {struct sig1} : Sigma :=
  match sig1 with
    star sig11 sig12 => star_assoc_left sig12 (star sig2 sig11)
    | _ => match sig2 with
             emp => sig1
             | _ => star sig2 sig1
           end
  end.

Lemma star_assoc_left_correct: forall sig1 sig2,
  Sigma_interp (star_assoc_left sig1 sig2) ==> Sigma_interp (star sig1 sig2).
Proof.
  induction sig1; induction sig2; simpl star_assoc_left; intros; auto.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  red; intros.
  generalize (IHsig1_2 _ s h H); intros.
  generalize entail_to_Sigma_impl; intro.
  red in H1.
  eapply H1; [auto | apply H0].
  Entail.
  
  red; intros.
  generalize (IHsig1_2 _ s h H); intros.
  generalize entail_to_Sigma_impl; intro.
  red in H1.
  eapply H1; [auto | apply H0].
  Entail.

  red; intros.
  generalize (IHsig1_2 _ s h H); intros.
  generalize entail_to_Sigma_impl; intro.
  red in H1.
  eapply H1; [auto | apply H0].
  Entail.

  red; intros.
  generalize (IHsig1_2 _ s h H); intros.
  generalize entail_to_Sigma_impl; intro.
  red in H1.
  eapply H1; [auto | apply H0].
  Entail.

  red; intros.
  generalize (IHsig1_2 _ s h H); intros.
  generalize entail_to_Sigma_impl; intro.
  red in H1.
  eapply H1; [auto | apply H0].
  Entail.

  eapply entail_to_Sigma_impl; Entail.

  eapply entail_to_Sigma_impl; Entail.

  eapply entail_to_Sigma_impl; Entail.

  eapply entail_to_Sigma_impl; Entail.

  eapply entail_to_Sigma_impl; Entail.
Qed.  

Lemma star_assoc_left_correct' : forall sig1 sig2,
  Sigma_interp (star sig1 sig2) ==> Sigma_interp (star_assoc_left sig1 sig2).
Proof.
  induction sig1; induction sig2; simpl star_assoc_left; intros; auto.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  
  red; intros.
  match goal with
    | |- Sigma_interp (star_assoc_left sig1_2 ?t) ?s ?h =>
      eapply (IHsig1_2 t s h)
  end.
  generalize entail_to_Sigma_impl; intro.
  red in H0.
  eapply H0; [auto | apply H].
  Entail.

  red; intros.
  match goal with
    | |- Sigma_interp (star_assoc_left sig1_2 ?t) ?s ?h =>
      eapply (IHsig1_2 t s h)
  end.
  generalize entail_to_Sigma_impl; intro.
  red in H0.
  eapply H0; [auto | apply H].
  Entail.

  red; intros.
  match goal with
    | |- Sigma_interp (star_assoc_left sig1_2 ?t) ?s ?h =>
      eapply (IHsig1_2 t s h)
  end.
  generalize entail_to_Sigma_impl; intro.
  red in H0.
  eapply H0; [auto | apply H].
  Entail.

  red; intros.
  match goal with
    | |- Sigma_interp (star_assoc_left sig1_2 ?t) ?s ?h =>
      eapply (IHsig1_2 t s h)
  end.
  generalize entail_to_Sigma_impl; intro.
  red in H0.
  eapply H0; [auto | apply H].
  Entail.

  red; intros.
  match goal with
    | |- Sigma_interp (star_assoc_left sig1_2 ?t) ?s ?h =>
      eapply (IHsig1_2 t s h)
  end.
  generalize entail_to_Sigma_impl; intro.
  red in H0.
  eapply H0; [auto | apply H].
  Entail.

  eapply entail_to_Sigma_impl; Entail.

  eapply entail_to_Sigma_impl; Entail.

  eapply entail_to_Sigma_impl; Entail.

  eapply entail_to_Sigma_impl; Entail.

  eapply entail_to_Sigma_impl; Entail.
Qed.  

Definition star_com (sig : Sigma) : Sigma :=
  match sig with
    star sig1 sig2 => star sig2 sig1
    | _ => sig
  end.

Lemma star_com_correct : forall sig,
  Sigma_interp (star_com sig) ==> Sigma_interp sig.
Proof.
  destruct sig; intros; simpl star_com; auto.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
Qed.

Lemma star_com_correct' : forall sig,
  Sigma_interp sig ==> Sigma_interp (star_com sig).
Proof.
  destruct sig; intros; simpl star_com; auto.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
  eapply entail_to_Sigma_impl; Entail.
Qed.

Definition rearrange_elim_common_subheap (pi : Pi) (sig1 sig2 : Sigma) : Sigma * Sigma :=
  match elim_common_subheap pi sig1 sig2 emp with
    | None => (remove_empty_heap pi (star_com (star_assoc_left sig1 emp)), sig2)
    | Some s => s
  end.

Lemma rearrange_elim_common_subheap_correct : forall sig1 sig2 pi sig1' sig2',
  rearrange_elim_common_subheap pi sig1 sig2 = (sig1',sig2') ->
  forall s,
    s |b= pi ->    
    (forall h, Sigma_interp sig1' s h -> Sigma_interp sig2' s h) ->
    (forall h, Sigma_interp sig1 s h -> Sigma_interp sig2 s h).
  simpl; intros.
  unfold rearrange_elim_common_subheap in H.
  generalize (elim_common_subheap_correct sig1 sig2 emp pi); intros.
  destruct (elim_common_subheap pi sig1 sig2 emp).
  destruct p.
  eapply H3.
  rewrite H; intuition.
  auto.
  intros.
  simpl in H4.
  Decompose_sepcon H4 h1 h2.
  red in H5.
  subst h1.
  cutrewrite (h0 = h2).
  auto.
  Equal_heap.
  simpl.
  Compose_sepcon h heap.emp; auto.
  red; auto.
  clear H3.
  injection H; clear H; intros; subst sig1' sig2'.
  apply H1.
  eapply remove_empty_heap_correct'.
  auto.
  generalize (star_com_correct'); intros.
  red in H.
  eapply H.
  clear H.
  generalize (star_assoc_left_correct'); intros.
  red in H.
  eapply H.
  clear H.  
  simpl.
  Compose_sepcon h heap.emp; auto.
  red; auto.
Qed.

Fixpoint elim_common_subheap_iterate (pi:Pi) (sig1 sig2:Sigma) (step:nat) {struct step} : Sigma * Sigma :=
  match step with
    | 0 => (sig1, sig2)
    | S n =>
      match rearrange_elim_common_subheap pi sig1 sig2 with
        | (sig1', sig2') => elim_common_subheap_iterate pi sig1' sig2' n
      end
  end.

Lemma elim_common_subheap_iterate_correct: forall n sig1 sig2 pi sig1' sig2',
  elim_common_subheap_iterate pi sig1 sig2 n = (sig1',sig2') ->
  forall s,
    s |b= pi ->    
    (forall h, Sigma_interp sig1' s h -> Sigma_interp sig2' s h) ->
    (forall h, Sigma_interp sig1 s h -> Sigma_interp sig2 s h).
  induction n; simpl; intros.
  injection H; clear H; intros; subst sig1' sig2'; auto.
  generalize (rearrange_elim_common_subheap_correct sig1 sig2 pi); intros.
  destruct (rearrange_elim_common_subheap pi sig1 sig2); try discriminate.
  eapply H3.
  intuition.
  auto.
  intros.
  eapply (IHn _ _ _ _ _ H); auto.
  auto.
Qed.

Transparent remove_empty_heap.

Fixpoint sigma_size (sig : Sigma) : nat :=
  match sig with
    | singl e1 e2 => 1
    | cell e1 => 1
    | lst e1 e2 => 3
    | star s1 s2 => sigma_size s1 + sigma_size s2
    | emp => 1
  end.

Inductive result (A : Set) : Set :=
  | Good : result A
  | Error : A -> result A.

Implicit Arguments Good [A].
Implicit Arguments Error [A].

Definition sigma_impl (pi:Pi) (sig1 sig2:Sigma)  : result (Sigma * Sigma) :=
  match elim_common_subheap_iterate pi sig1 sig2 ((sigma_size sig1 + sigma_size sig2) * 2) with
    | (emp, emp) => Good
    | e => Error e
  end.

Lemma sigma_impl_correct: forall sig1 sig2 pi,
  sigma_impl pi sig1 sig2 = Good ->
  forall s,
    s |b= pi ->    
    (forall h, Sigma_interp sig1 s h -> Sigma_interp sig2 s h).
Proof.
  intros.
  unfold sigma_impl in H.
  generalize (elim_common_subheap_iterate_correct ((sigma_size sig1 + sigma_size sig2) * 2) sig1 sig2 pi); intros.
  destruct (elim_common_subheap_iterate pi sig1 sig2 ((sigma_size sig1 + sigma_size sig2) * 2)); simpl in H; try discriminate.
  apply (H2 _ _ (refl_equal _) _ H0); clear H2; auto.
  intros.
  destruct s0; destruct s1; simpl in H; try discriminate; auto.
Qed.

Definition frag_entail_fct (a1 a2 : assrt) : result (assrt * assrt) :=
  let (pi1, sig1) := a1 in 
    let (pi2, sig2) := a2 in 
      if expr_b_dp (!pi1) then (* verifying if the lhs logical part is not a contradiction *)
        (*Error ((pi1, emp), (pi2, emp)) *)
        Good
        else      
          match sigma_impl pi1 sig1 sig2 with (* else try to prove the implication of abstract heaps*)
            | Good => if expr_b_dp (pi1 =b> pi2) then (* and implication of logical parts *)
              Good 
              else 
                Error ((pi1, emp), (pi2, emp))
            | Error (s1, s2) => Error ((pi1, s1), (pi2, s2))
          end.

Lemma frag_entail_fct_correct: forall a1 a2,
  frag_entail_fct a1 a2 = Good ->
  (assrt_interp a1 ==> assrt_interp a2).
Proof.
  destruct a1; destruct a2; red; unfold frag_entail_fct; simpl; intros.
  generalize (expr_b_dp_correct (!p)); intros.
  destruct (expr_b_dp (!p)); simpl in H; try discriminate.
  inversion_clear H0.
  generalize (H1 (refl_equal _) s1); intros.
  unfold eval_pi in H2.
  Omega_exprb.  
  clear H1.
  split.
  destruct (sigma_impl p s s0).
  inversion_clear H0.
  generalize (expr_b_dp_correct (p =b> p0)); intros.
  destruct (expr_b_dp (p =b> p0)); simpl in H; try discriminate.
  generalize (H0 (refl_equal _) s1); intros.
  unfold eval_pi.
  unfold eval_pi in H1.
  Omega_exprb.
  destruct p1; try discriminate.
  inversion_clear H0.
  eapply (sigma_impl_correct s s0 p).
  destruct (sigma_impl p s s0); try discriminate; auto.
  destruct p1; try discriminate.
  auto.
  auto.
Qed.

(*
   Ici ajouter une fonction pour rajouter les contraintes implicites
*)
(*
Pour plus tard: simplifier les expr_b

Fixpoint simpl_expr_b (pi: expr_b) : epxr_b :=
  match pi with
    | pi1 &&& pi2 =>
      match (simpl_expr_b pi1, simpl_expr_b pi2) with
        | (!true_b,_) => 
        |
        

    | _ => if (expr_b_dp pi) then
              true_b else if
                if (expr_b_dp (!pi)) then
                  (! true_b)
  end.
*)       

Definition compute_constraint_cell (pi : Pi) (sig1 sig2 : Sigma) : Pi :=
  match (sig1,sig2) with
    | (singl e1 e2, singl e3 e4) => 
      if expr_b_dp (pi =b> (e1 =/= e3)) then pi else
        pi &&& (e1 =/= e3)
    | (singl e1 e2, cell e3) => 
      if expr_b_dp (pi =b> (e1 =/= e3)) then pi else
        pi &&& (e1 =/= e3)
    | (cell e1, singl e3 e4) => 
      if expr_b_dp (pi =b> (e1 =/= e3)) then pi else 
        pi &&& (e1 =/= e3)
    | (cell e1, cell e3) => 
      if expr_b_dp (pi =b> (e1 =/= e3)) then pi else 
        pi &&& (e1 =/= e3)
    | (singl e1 e2, lst e3 e4) => 
      if expr_b_dp (pi =b> (e3 =/= e4)) then
        if expr_b_dp (pi =b> (e1 =/= e3)) then pi else 
          pi &&& (e1 =/= e3) 
        else pi
    | (lst e1 e2, singl e3 e4) => 
      if expr_b_dp (pi =b> (e1 =/= e2)) then
        if expr_b_dp (pi =b> (e1 =/= e3)) then pi else 
          pi &&& (e1 =/= e3) 
        else pi
    | (cell e1, lst e3 e4) =>  
      if expr_b_dp (pi =b> (e3 =/= e4)) then
        if expr_b_dp (pi =b> (e1 =/= e3)) then pi else 
          pi &&& (e1 =/= e3) 
        else pi
    | (lst e1 e2, cell e3) => 
      if expr_b_dp (pi =b> (e1 =/= e2)) then
        if expr_b_dp (pi =b> (e1 =/= e3)) then pi else 
          pi &&& (e1 =/= e3) 
        else pi
    | (lst e1 e2, lst e3 e4) => 
      if expr_b_dp (pi =b> (e1 =/= e2)) && expr_b_dp (pi =b> (e3 =/= e4)) then
        if expr_b_dp (pi =b> (e1 =/= e3)) then pi else 
          pi &&& (e1 =/= e3) 
        else pi
    | (_, _) => pi

  end.

Lemma compute_constraint_cell_correct: forall sig1 sig2 pi,
  assrt_interp (pi,star sig1 sig2) ==> assrt_interp ((compute_constraint_cell pi sig1 sig2), star sig1 sig2).
Proof.
  destruct sig1; destruct sig2; red; simpl; intros; auto; unfold compute_constraint_cell; inversion_clear H; split.
  
  generalize (expr_b_dp_correct (pi =b> e =/= e1)); intros.
  destruct (expr_b_dp (pi =b> e =/= e1)); auto.
  clear H.
  simpl; eapply andb_true_intro.
  split; auto.
  symmetry; eapply negb_sym; eapply Zeq_bool_false''.
  Decompose_sepcon H1 h1 h2.
  eapply singl_disjoint_neq.
  apply H3.
  apply H1.
  Disjoint_heap.
  auto.

  generalize (expr_b_dp_correct (pi =b> e =/= e1)); intros.
  destruct (expr_b_dp (pi =b> e =/= e1)); auto.
  clear H.
  simpl; eapply andb_true_intro.
  split; auto.
  symmetry; eapply negb_sym; eapply Zeq_bool_false''.
  Decompose_sepcon H1 h1 h2.
  inversion_clear H1.
  eapply singl_disjoint_neq.
  apply H3.
  apply H4.
  Disjoint_heap.
  auto.

  generalize (expr_b_dp_correct (pi =b> e1 =/= e2)); intros.
  destruct (expr_b_dp (pi =b> e1 =/= e2)); auto.
  Decompose_sepcon H1 h1 h2.
  destruct H5.
  generalize (H (refl_equal _) s); intros.
  unfold eval_pi.
  unfold eval_pi in H0.  
  Omega_exprb.
  generalize (expr_b_dp_correct (pi =b> e =/= e1)); intros.
  destruct (expr_b_dp (pi =b> e =/= e1)); auto.
  clear H12.
  simpl; eapply andb_true_intro.
  split; auto.
  symmetry; eapply negb_sym; eapply Zeq_bool_false''.
  Decompose_sepcon H10 h21 h22.
  eapply singl_disjoint_neq.
  apply H4.
  apply H12.
  Disjoint_heap.
  auto.

  generalize (expr_b_dp_correct (pi =b> e =/= e0)); intros.
  destruct (expr_b_dp (pi =b> e =/= e0)); auto.
  clear H.
  simpl; eapply andb_true_intro.
  split; auto.
  symmetry; eapply negb_sym; eapply Zeq_bool_false''.
  Decompose_sepcon H1 h1 h2.
  inversion_clear H3.
  eapply singl_disjoint_neq.
  apply H4.
  apply H1.
  Disjoint_heap.
  auto.

  generalize (expr_b_dp_correct (pi =b> e =/= e0)); intros.
  destruct (expr_b_dp (pi =b> e =/= e0)); auto.
  clear H.
  simpl; eapply andb_true_intro.
  split; auto.
  symmetry; eapply negb_sym; eapply Zeq_bool_false''.
  Decompose_sepcon H1 h1 h2.
  inversion_clear H3.
  inversion_clear H1.
  eapply singl_disjoint_neq.
  apply H4.
  apply H3.
  Disjoint_heap.
  auto.

  generalize (expr_b_dp_correct (pi =b> e0 =/= e1)); intros.
  destruct (expr_b_dp (pi =b> e0 =/= e1)); auto.
  Decompose_sepcon H1 h1 h2.
  inversion_clear H4.
  destruct H5.
  generalize (H (refl_equal _) s); intros.
  unfold eval_pi in H0.
  unfold eval_pi in H7.
  Omega_exprb.
  generalize (expr_b_dp_correct (pi =b> e =/= e1)); intros.
  destruct (expr_b_dp (pi =b> e =/= e1)); auto.
  clear H12.
  simpl; eapply andb_true_intro.
  split; auto.
  symmetry; eapply negb_sym; eapply Zeq_bool_false''.
  Decompose_sepcon H10 h21 h22.
  eapply singl_disjoint_neq.
  apply H2.
  apply H12.
  Disjoint_heap.
  auto.

  generalize (expr_b_dp_correct (pi =b> e =/= e0)); intros.
  destruct (expr_b_dp (pi =b> e =/= e0)); auto.
  Decompose_sepcon H1 h1 h2.
  destruct H2.
  generalize (H (refl_equal _) s); intros.
  unfold eval_pi in H0.
  unfold eval_pi in H7.  
  Omega_exprb.
  generalize (expr_b_dp_correct (pi =b> e0 =/= e1)); intros.
  destruct (expr_b_dp (pi =b> e0 =/= e1)); auto.
  clear H12.
  simpl; eapply andb_true_intro.
  split; auto.
  symmetry; eapply negb_sym; eapply Zeq_bool_false''.
  Decompose_sepcon H10 h11 h12.
  eapply singl_disjoint_neq.
  apply H12.
  apply H4.
  Disjoint_heap.
  auto.

  generalize (expr_b_dp_correct (pi =b> e =/= e0)); intros.
  destruct (expr_b_dp (pi =b> e =/= e0)); auto.
  Decompose_sepcon H1 h1 h2.
  inversion_clear H4.
  destruct H2.
  generalize (H (refl_equal _) s); intros.
  unfold eval_pi in H0.
  unfold eval_pi in H7.  
  Omega_exprb.
  generalize (expr_b_dp_correct (pi =b> e0 =/= e1)); intros.
  destruct (expr_b_dp (pi =b> e0 =/= e1)); auto.
  clear H12.
  simpl; eapply andb_true_intro.
  split; auto.
  symmetry; eapply negb_sym; eapply Zeq_bool_false''.
  Decompose_sepcon H10 h11 h12.
  eapply singl_disjoint_neq.
  apply H12.
  apply H5.
  Disjoint_heap.
  auto.

  generalize (expr_b_dp_correct (pi =b> e =/= e0)); intros.
  destruct (expr_b_dp (pi =b> e =/= e0)); auto.
  generalize (expr_b_dp_correct (pi =b> e1 =/= e2)); intros.
  destruct (expr_b_dp (pi =b> e1 =/= e2)); auto.
  simpl.
  generalize (expr_b_dp_correct (pi =b> e =/= e1)); intros.
  destruct (expr_b_dp (pi =b> e =/= e1)); auto.
  Decompose_sepcon H1 h1 h2.
  destruct H4.
  generalize (H (refl_equal _) s); intros.
  unfold eval_pi in H0.
  unfold eval_pi in H8.   
  Omega_exprb.
  destruct H7.
  generalize (H2 (refl_equal _) s); intros.
  unfold eval_pi in H0.
  unfold eval_pi in H14.
  Omega_exprb.
  simpl; eapply andb_true_intro.
  split; auto.
  rewrite Zeq_bool_false''.
  auto.
  Decompose_sepcon H11 h11 h12.
  Decompose_sepcon H17 h41 h42.
  eapply singl_disjoint_neq.
  apply H19.
  apply H21.
  Disjoint_heap.
  auto.
Qed.

Fixpoint compute_constraint_cell_sigma (pi: Pi) (sig1 sig2:Sigma) {struct sig2} : Pi :=
  match sig2 with
    | star sig21 sig22 => compute_constraint_cell_sigma  (compute_constraint_cell_sigma pi sig1 sig21) sig1 sig22
    | _ => compute_constraint_cell pi sig1 sig2
  end.

Lemma compute_constraint_cell_sigma_correct: forall sig2 sig1 pi,
  assrt_interp (pi,star sig1 sig2) ==> assrt_interp ((compute_constraint_cell_sigma pi sig1 sig2 ),star sig1 sig2).  
Proof.
  induction sig2; simpl compute_constraint_cell_sigma; intros; try (eapply compute_constraint_cell_correct).
  simpl; red; intros.
  simpl in IHsig2_1; red in IHsig2_1.
  simpl in IHsig2_2; red in IHsig2_2.
  inversion_clear H.
  split; auto.
  Decompose_sepcon H1 h1 h2.
  Decompose_sepcon H4 h21 h22.
  assert (
    (s |b= compute_constraint_cell_sigma pi sig1 sig2_1) /\
    (Sigma_interp sig1 ** Sigma_interp sig2_1) s (h1 +++ h21)
  ).
  eapply IHsig2_1.
  split; auto.
  Compose_sepcon h1 h21; auto.
  inversion_clear H6.
  clear H9.
  assert (
    (s |b= compute_constraint_cell_sigma (compute_constraint_cell_sigma pi sig1 sig2_1) sig1 sig2_2 ) /\
    (Sigma_interp sig1 ** Sigma_interp sig2_2) s (h1 +++ h22)
  ).
  eapply IHsig2_2.
  split; auto.
  Compose_sepcon h1 h22; auto.
  inversion_clear H6.
  auto.
Qed.

Fixpoint compute_constraints' (pi: Pi) (sig:Sigma)  {struct sig} : Pi :=
  match sig with
    | star sig1 sig2 => compute_constraints' (compute_constraint_cell_sigma pi sig2 sig1) sig1 
    | _ => pi
  end.

Lemma compute_constraints'_correct: forall sig pi,
  assrt_interp (pi,sig) ==> assrt_interp ((compute_constraints' pi sig), sig).  
  induction sig; simpl compute_constraints'; intros; red; intros; auto.

  inversion_clear H; split; auto.
  simpl in H1.
  Decompose_sepcon H1 h1 h2.
  assert (assrt_interp ((compute_constraint_cell_sigma pi sig2 sig1), star sig2 sig1) s h).
  generalize compute_constraint_cell_sigma_correct; intros.
  red in H3; eapply H3.
  split; auto.
  Compose_sepcon h2 h1; auto.
  inversion_clear H3.
  assert (assrt_interp (compute_constraints' (compute_constraint_cell_sigma pi sig2 sig1) sig1 , sig1) s h1).
  red in IHsig1; eapply IHsig1.
  split; auto.
  inversion_clear H3; auto.
Qed.

Definition compute_constraints (pi : Pi) (sig : Sigma)  : Pi :=
  compute_constraints' pi (star_assoc_left sig emp).

Lemma compute_constraints_correct: forall pi sig,
  (assrt_interp (pi,sig) ==> assrt_interp (compute_constraints pi sig, sig)).
Proof.
  unfold compute_constraints.
  red; intros.
  generalize compute_constraints'_correct; intros.
  red in H0.
  cut (
    assrt_interp (compute_constraints' pi (star_assoc_left sig emp), (star_assoc_left sig emp)) s h
  ).
  intros.
  inversion_clear H1.  
  split; auto.
  generalize (star_assoc_left_correct sig emp); intros.
  red in H1.
  generalize ( H1 _ _ H3); intros.
  simpl in H4.
  Decompose_sepcon H4 h1 h2.
  red in H8.
  subst h2.
  cutrewrite (h = h1); auto.
  Equal_heap.
  eapply H0; auto.
  inversion_clear H.
  split; auto.
  generalize (star_assoc_left_correct' sig emp); intros.
  red in H; eapply H.
  simpl.
  Compose_sepcon  h heap.emp; auto.
  red; auto.
Qed.

Fixpoint cell_loc_not_null (pi : Pi) (sig : Sigma)  {struct sig} : Pi :=
  match sig with
    | emp => pi
    | lst e1 e2 => pi
    | cell e1 => 
      if expr_b_dp (pi =b> (e1 =/= nat_e 0)) then pi else 
          pi &&& (e1 =/= (nat_e 0)) 
    | (singl e1 e2) => 
      if expr_b_dp (pi =b> (e1 =/= nat_e 0)) then pi else 
          pi &&& (e1 =/= nat_e 0) 
    | star s1 s2 =>
      cell_loc_not_null (cell_loc_not_null pi s1) s2 
  end.

Lemma cell_loc_not_null_correct: forall sig pi,
  assrt_interp (pi,sig) ==> assrt_interp ((cell_loc_not_null pi sig), sig).
  induction sig; simpl; red; intros; auto.
  
  decompose [and]  H; clear H.
  generalize (expr_b_dp_correct (pi =b> e =/= (nat_e 0))); intros.
  destruct (expr_b_dp (pi =b> e =/= (nat_e 0))); auto.
  clear H.
  split; auto.  
  unfold eval_pi; unfold eval_pi in H0.
  Omega_exprb.

  decompose [and]  H; clear H.
  generalize (expr_b_dp_correct (pi =b> e =/= (nat_e 0))); intros.
  destruct (expr_b_dp (pi =b> e =/= (nat_e 0))); auto.
  clear H.
  split; auto.
  unfold eval_pi; unfold eval_pi in H0.
  Omega_exprb.
  
  inversion_clear H.
  split; auto.
  Decompose_sepcon H1 h1 h2.
  red in IHsig1.
  red in IHsig2.
  assert (assrt_interp (cell_loc_not_null pi sig1, sig1) s h1).
  eapply IHsig1.
  split; auto.
  inversion_clear H3.
  assert (assrt_interp (cell_loc_not_null pi sig1, sig2) s h2).
  split; auto.
  eapply (proj1 (IHsig2 (cell_loc_not_null pi sig1) s h2 H3)).
Qed.

Definition assrt_entail_fct (a1 a2: assrt) : result (assrt * assrt) :=
  let (pi1,sig1) := a1 in frag_entail_fct (compute_constraints (cell_loc_not_null pi1 sig1) sig1 , sig1) a2 .

Lemma assrt_entail_fct_correct: forall a1 a2,
  assrt_entail_fct a1 a2 = Good ->
  (assrt_interp a1 ==> assrt_interp a2).
  red; unfold assrt_entail_fct; intros.
  destruct a1.
  generalize (frag_entail_fct_correct); intros.
  eapply (H1 (compute_constraints (cell_loc_not_null p s0) s0, s0) a2 H).
  generalize (compute_constraints_correct); intros.
  red in H2; eapply H2.
  generalize (cell_loc_not_null_correct); intros.
  red in H3; eapply H3.
  auto.
Qed.

(*
Goal   (assrt_interp P) ==> (assrt_interp Q).
  eapply frag_impl_correct.
  unfold P; unfold Q; unfold x1; unfold x2; unfold x3; unfold x4 ; unfold x5; unfold x6; unfold null.  
  auto.
  simpl.
Qed.
*)


(* 

Our goal here is to verify entailments of the form:

 <P | S> |- \/i <Pi | Si>

To achieve such goal we have a decision procedure for arithmetic (expr_b_dp),
and a decision procedure (assrt_entail_fct) for entailments of the form:

<P|S> |- <P'|S'>                

We propose the two following rules :

*)

(*

rule 1 is intuitive:

\/i <P|S> |- <Pi |Si>
-------------------------- (rule 1)
<P|S> |- \/i <Pi | Si>

orassrt_impl_Assrt1 try to prove (\/i <P|S> |- <Pi |Si>)

and give the subgoals that were not resolved

*)    

Fixpoint orassrt_impl_Assrt1 (a:assrt) (A:Assrt) (l:list (assrt * assrt)) {struct A} : result (list (assrt * assrt)) :=
  match A with
    | nil => Error l
    | hd::tl =>
      match assrt_entail_fct a hd with
        | Good => Good
        | Error e => orassrt_impl_Assrt1 a tl (e :: l)
      end
  end.

(* This lemma prove that the rule 1 is correct *)

Lemma orassrt_impl_Assrt1_correct: forall A a l,
  orassrt_impl_Assrt1 a A l = Good ->
  (assrt_interp a ==> Assrt_interp A).
  induction A; red; simpl; intros; try discriminate.
  generalize (assrt_entail_fct_correct a0 a); intros.
  destruct (assrt_entail_fct a0 a).
  left.
  intuition.
  clear H1.
  right.
  apply (IHA _ _ H s h H0).
Qed.

(*

However rule 1 is sometime too weak to solve some entailments.

For example:

<True | x |-> e> |- <e == 0| x |-> 0> \/ <e =/= 0 | x |-> e>

(such disjunctions may appear in loops invariants)
 
To solve such goals we proposed the folowing rule:



P -> \/i Pi               /\i <P /\ Pi | S> |- <true, Si>
---------------------------------------------------------- (rule 2)
                 <P | S> |- \/i <Pi | Si>

*)


(* orpi compute the term \/i Pi *)

Fixpoint orpi (l: list assrt) : expr_b :=
  match l with
    | nil => neg_b true_b
    | (pi, sig) :: tl => pi ||| (orpi tl)
  end.

(* orassrt_impl_Assrt2 try to prove  ( /\i <P /\ Pi | S> |- <true, Si>)
   and give the subgoals that were not resolved
*)

Fixpoint orassrt_impl_Assrt2 (a:assrt) (A:Assrt) (l:list (assrt * assrt)) {struct A} : result (list (assrt * assrt)) :=
  match A with
    | nil => Error l
    | (pi, sig) :: tl =>
      match a with
        | (pi', sig') =>
          match sigma_impl (pi' &&& pi) sig' sig  with
            | Error (s1, s2) => Error (((pi', s1), (pi, s2)) :: l)
            | Good => 
              match tl with
                | nil => Good
                | _ => orassrt_impl_Assrt2 a tl l
              end
          end
      end
  end.

(* This lemma prove that the rule 2 is correct *)

Lemma orassrt_impl_Assrt2_correct: forall A pi sig l,
  orassrt_impl_Assrt2 (pi, sig) A l = Good -> (* /\i <P /\ Pi | S> |- <true, Si> *)
  forall s h,
    s |b= pi =b> (orpi A) ->  (* P -> \/i Pi *)
    ((assrt_interp (pi,sig)) s h -> (Assrt_interp A) s h). (* <P | S> |- \/i <Pi | Si> *)
  induction A; intros; try discriminate.
  simpl.
  destruct a.
  simpl in H1; simpl orpi in H0.
  inversion_clear H1.
  simpl in H.
  generalize (sigma_impl_correct sig s0 (pi &&& p)); intros.
  destruct (sigma_impl (pi &&& p) sig s0).
  assert ((s |b= p ||| orpi A)).
  unfold eval_pi in H2.
  Omega_exprb.
  assert ((s |b= p) \/ (s |b= orpi A)).
  simpl in H4; simpl.
  destruct (eval_b p s); destruct (eval_b (orpi A) s); simpl in H4; try discriminate; auto.
  inversion_clear H5.
  left.
  simpl; split.
  auto.
  eapply H1; auto.
  unfold eval_pi in H2.
  Omega_exprb.  
  destruct A.
  simpl in H6.
  discriminate.  
  right.
  eapply IHA.
  apply H.
  unfold eval_pi in H2.
  Omega_exprb.
  split; auto.
  destruct p0.
  discriminate.
Qed.


(* entry point *)

Definition entail_fct (a:assrt) (A:Assrt) (l:list (assrt * assrt)) : result (list (assrt * assrt)) :=
  match a with
    | (pi, sig) =>
      if expr_b_dp (pi =b> (orpi A)) then (* if P -> \/i Pi *)
        match orassrt_impl_Assrt2 a A nil with (* then try rule 2*)
          | Good => Good
          | Error e => orassrt_impl_Assrt1 a A nil (* if rule 2 failed then try rule 1 fi*)
        end
        else
          orassrt_impl_Assrt1 a A nil (* else try directly rule 1 fi *)
  end.

Lemma entail_fct_correct: forall A a l,
  entail_fct a A l = Good ->
  (assrt_interp a ==> Assrt_interp A).
  intros.
  red; intros.
  unfold entail_fct in H.
  destruct a.
  generalize (expr_b_dp_correct (p =b> orpi A)); intros.
  destruct (expr_b_dp (p =b> orpi A)); try discriminate.
  generalize (orassrt_impl_Assrt2_correct A p s0 nil); intros.
  destruct (orassrt_impl_Assrt2 (p, s0) A nil).
  apply H2; auto.
  clear H2 H1.
  generalize orassrt_impl_Assrt1_correct; intros.
  red in H1; eapply H1.
  apply H.
  auto.
  clear H1.
  generalize orassrt_impl_Assrt1_correct; intros.
  red in H1; eapply H1.
  apply H.
  auto.
Qed.

(* This function is only used by bigtoe, to provide verification of entailments  *)

Fixpoint Assrt_entail_Assrt_dp (A1 A2: Assrt) (l: list (assrt * assrt)) {struct A1} : result (list (assrt * assrt)) :=
  match A1 with
    | nil => Good
    | hd::tl =>
      match entail_fct hd A2 nil with
        | Good => Assrt_entail_Assrt_dp tl A2 l
        | Error e => Error (e ++ l)
      end
  end.

Lemma Assrt_entail_Assrt_dp_correct: forall A1 A2 l,
  Assrt_entail_Assrt_dp A1 A2 l = Good ->
  (Assrt_interp A1) ==> (Assrt_interp A2).
Proof.
  induction A1; red; simpl; intros; try contradiction.
  generalize (entail_fct_correct A2 a nil); intros.
  destruct (entail_fct a A2); try discriminate.
  inversion_clear H0.
  apply (H1 (refl_equal _) s h H2).
  apply (IHA1 _ _ H s h H2).
Qed.


