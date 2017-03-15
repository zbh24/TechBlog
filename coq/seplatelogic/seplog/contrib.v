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
Require Import util_tactic.
Require Import heap.
Require Import heap_tactic.
Require Import bipl.
Require Import axiomatic.

Open Local Scope heap_scope.
Open Local Scope sep_scope.

Load contrib_tactics.

(*
 * update_store2, update_heap2, etc. properties 
 *)

Lemma singleton_equal: forall s h1 h2 e1 e2 e3 e4,
  (e1 |-> e2) s h1 ->
  (e3 |-> e4) s h2 ->
  eval e1 s = eval e3 s ->
  eval e2 s = eval e4 s ->
  h1 = h2.
  intros.
  red in H.
  red in H0.
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H3.
  inversion_clear H.
  rewrite H1 in H0.
  rewrite H0 in H3.
  injection H3.
  intros.
  subst x0.
  rewrite H2 in H4.
  rewrite H4; rewrite H5; auto.
Qed.

Lemma semax_lookup_simple: forall R e e' x s h,
  ((e |-> e') ** TT) s h ->
  (update_store2 x e' R) s h ->
  exists e0, ((e |-> e0) ** ((e |-> e0) -* (update_store2 x e0 R))) s h.
  intros.
  Decompose_sepcon H h1 h2.
  exists e'.
  Compose_sepcon h1 h2.
  auto.
  Intro_sepimp h1' h'.
  assert (h1' = h1). 
  eapply singleton_equal; [apply H5 | apply H1 | auto | auto].
  assert (h' = h).
  subst h1'.
  Equal_heap.
  rewrite H8; auto.
Qed. 

Lemma update_heap2_sep_con: forall x v P Q,
  (update_heap2 x v P) ** Q ==> update_heap2 x v (P**Q).
  red; intros.
  inversion_clear H.
  inversion_clear H0.
  decompose [and] H; clear H.
  red in H1.
  inversion_clear H1.
  inversion_clear H.
  inversion_clear H3.
  inversion_clear H.
  red.
  exists x2; split; auto.
  exists x3; split.
  rewrite H2.
  apply heap.lookup_union; auto.
  exists (heap.update x2 (eval v s) x0).
  exists x1.
  split.
  apply heap.disjoint_update.
  auto.
  split.
  rewrite H2.
  eapply heap.equal_update_L.
  auto.
  apply H3.
  auto.
Qed.

Lemma update_heap2_sep_con': forall P Q x1 x2 v1 v2,
  (update_heap2 x1 v1 P) ** (update_heap2 x2 v2 Q) ==>
  update_heap2 x1 v1 (update_heap2 x2 v2 (P**Q)).
  red; intros.
  generalize (update_heap2_sep_con x1 v1 P (update_heap2 x2 v2 Q)); intro.
  red in H0.
  generalize (H0 _ _ H); intro.
  red.
  red in H1.
  inversion_clear H1 as [p].
  inversion_clear H2.
  inversion_clear H3 as [z].
  exists p.
  split; auto.
  exists z.
  inversion_clear H2.
  split; auto.
  rewrite sep.con_com_equiv.
  apply (update_heap2_sep_con x2 v2 Q P).
  rewrite sep.con_com_equiv.
  auto.
Qed.

(*
 * variations of Reynolds' axioms
 *)

Lemma semax_assign' :forall Q P x e,
   (P ==> update_store2 x e Q) -> 
   {{ P }} x <- e {{ Q }}.
intros.
apply semax_strengthen_pre with (update_store2 x e Q) .
auto.
apply semax_assign.
Qed.

Lemma semax_assign'' : forall R P Q x e c,
  (P ==> update_store2 x e R) ->
  {{ R }} c {{ Q }} ->
  {{ P }} x <- e ; c {{ Q }}.
intros.
apply semax_seq with R.
apply semax_assign'.
auto.
auto.
Qed.

Lemma semax_lookup' : forall Q P x e,
  (P ==> lookup2 x e Q) -> 
  {{ P }} x <-* e {{ Q }}.
intros.
apply semax_strengthen_pre with (lookup2 x e Q) .
auto.
apply semax_lookup.
Qed.

Lemma semax_lookup'' : forall R P Q x e c,
  (P ==> lookup2 x e R) ->
  {{ R }} c {{ Q }} ->
  {{ P }} x <-* e ; c {{ Q }}.
intros.
apply semax_seq with (Q:=R).
apply semax_lookup'.
auto.
auto.
Qed.

Lemma semax_lookup_backwards' : forall P Q x e,
  (P ==> (fun s h => exists e0, ((e |-> e0) ** ((e |-> e0) -* (update_store2 x e0 Q))) s h)) -> 
  {{ P }} x <-* e {{ Q }}.
intros.
apply semax_strengthen_pre with (fun s => fun h =>
    exists e0, ((e |-> e0) ** ((e |-> e0) -* (update_store2 x e0 Q))) s h).
auto.
apply semax_lookup_backwards.
Qed.

Lemma semax_lookup_backwards'' : forall P Q R x e c,
  (P ==> (fun s h =>
    exists e0, ((e |-> e0) ** ((e |-> e0) -* (update_store2 x e0 R))) s h)) -> 
  {{ R }} c {{ Q }} ->
  {{ P }} x <-* e; c {{ Q }}.
intros.
apply semax_seq with (Q:=R).
apply semax_strengthen_pre with (fun s => fun h =>
    exists e0, ((e |-> e0) ** ((e |-> e0) -* (update_store2 x e0 R))) s h).
auto.
apply semax_lookup_backwards.
auto.
Qed.

Lemma cell_read: forall e v Q s h,
 ((e |-> v) ** TT) s h /\ Q s h ->
 ((e |-> v) ** ((e |-> v) -* Q)) s h.
  intros.
  inversion_clear H.
  Decompose_sepcon H0 h1 h2.
  Compose_sepcon h1 h2; auto.
  Intro_sepimp h1' h'.
  assert (h1' = h1).
  eapply singleton_equal.
  apply H5.
  apply H0.
  auto.
  auto.
  subst h1'.
  assert (h' = h).
  Heap_emp_clean; Equal_heap.
  rewrite H7; auto.
Qed.

Lemma semax_lookup_backwards''2 : forall P Q R x e c,
  (P ==> (fun s h => exists e0, ((e |-> e0) ** TT) s h /\ (update_store2 x e0 R) s h)) -> 
  {{ R }} c {{ Q }} ->
  {{ P }} x <-* e; c {{ Q }}.
  intros.
  apply semax_lookup_backwards'' with R.
  red; intros.
  generalize (H _ _ H1); intro.
  inversion_clear H2.
  exists x0.
  apply cell_read.
  assumption.
  assumption.
Qed.

Lemma semax_mutation' : forall Q P e1 e2,
  (P ==> update_heap2 e1 e2 Q) -> 
  {{ P }} e1 *<- e2 {{ Q }}.
intros.
apply semax_strengthen_pre with (update_heap2 e1 e2 Q) .
auto.
apply semax_mutation.
Qed.

Lemma semax_mutation'' : forall R P Q c e1 e2,
  (P ==> update_heap2 e1 e2 R) ->
  {{ R }} c {{ Q }} ->
  {{ P }} e1 *<- e2 ; c {{ Q }}.
intros.
apply semax_seq with (Q:=R).
apply semax_mutation'.
auto.
auto.
Qed.

Lemma semax_mutation_backwards' : forall Q P e1 e2,
  (P ==> (fun s h => exists e'', ((e1 |-> e'') ** ((e1 |-> e2) -* Q)) s h)) -> 
  {{ P }} e1 *<- e2 {{ Q }}.
intros.
apply semax_strengthen_pre with (fun s => fun h =>
    exists e'', ((e1 |-> e'') ** ((e1 |-> e2) -* Q)) s h).
auto.
apply semax_mutation_backwards.
Qed.

Lemma semax_mutation_backwards'' : forall Q P R e1 e2 c,
  (P ==> (fun s h => exists e'', ((e1 |-> e'') ** ((e1 |-> e2) -* R)) s h)) -> 
  {{ R }} c {{ Q }} -> 
  {{ P }} e1 *<- e2 ; c {{ Q }}.
intros.
apply semax_seq with (Q:=R).
apply semax_mutation_backwards'.
auto.
auto.
Qed.

Lemma semax_while' : forall b c I P Q,
  (P ==> I) ->
  {{ fun s h => I s h /\ eval_b b s = true }} c {{ I }} ->
  ((fun s h => I s h /\ eval_b b s = false) ==> Q) ->
  {{ P }} while b c {{ Q }}.
intros.
apply semax_weaken_post with (fun s => fun h => I s h /\ eval_b b s = false).
auto.
apply semax_strengthen_pre with I.
auto.
apply semax_while.
auto.
Qed.

Lemma semax_while'': forall b c I P Q c1,
  (P ==> I) ->
  {{ fun s h => I s h /\ eval_b b s = true }} c {{ I }} ->
  {{ fun s h => I s h /\ eval_b b s = false }} c1 {{ Q }} ->
  {{ P }} while b c; c1 {{ Q }}.
intros.
apply semax_seq with (fun s => fun h => I s h /\ eval_b b s = false).
eapply semax_while'.
red; intros.
apply H.
auto.
auto.
red; intros.
auto.
auto.
Qed.

Lemma semax_skip': forall P Q,
  (P ==> Q) -> 
  {{ P }} skip {{ Q }}.
intros.
apply semax_strengthen_pre with Q.
auto.
apply semax_skip.
Qed.

Lemma apply_triple: forall (P P' Q Q': assert) c,
   {{P'}} c {{Q'}} ->
   (P ==> P') ->
   (Q' ==> Q) ->
   {{P}} c {{Q}}.
intros.
apply semax_strengthen_pre with P'.
auto.
apply semax_weaken_post with Q'.
auto.
auto.
Qed.

Lemma apply_triple': forall (P P' Q Q': assert) c c',
   {{P'}} c {{Q'}} ->
   (P ==> P') ->
   {{Q'}} c' {{Q}} ->
   {{P}} c; c' {{Q}}.
intros.
apply semax_seq with Q'.
apply semax_strengthen_pre with P'.
auto.
auto.
auto.
Qed.

Lemma semax_and' : forall c P Q, {{ P }} c {{ Q }} -> 
  forall P' Q' d, {{ P' }} d {{ Q' }} ->
    c = d ->
    {{ And P P' }} c {{ And Q Q' }}.
do 4 intro.
induction H.
(* case skip *)
intros.
generalize P H0; clear P H0.
induction H; intros; try discriminate.
constructor.
apply semax_conseq with (And P0 P') (And P0 Q').
unfold And.
red; intros.
split; try tauto.
apply H; try tauto.
unfold And.
red; intros.
split; try tauto.
apply H0; try tauto.
apply IHsemax; auto.
(* case assign *)
intros.
generalize P x e H0; clear P x e H0.
induction H; intros; try discriminate.
injection H0; clear H0; intros; subst x0 e0.
apply semax_assign'.
unfold And; unfold update_store2.
red; intros.
auto.
apply semax_conseq with (And (update_store2 x e P0) P') (And P0 Q').
unfold And.
red; intros.
split; try tauto.
apply H; try tauto.
unfold And.
red; intros.
split; try tauto.
apply H0; try tauto.
apply IHsemax; auto.
(* case lookup *)
intros.
generalize P x e H0; clear P x e H0.
induction H; intros; try discriminate.
injection H0; clear H0; intros; subst x0 e0.
apply semax_lookup'.
unfold And; unfold lookup2.
red; intros.
inversion_clear H.
inversion_clear H0.
inversion_clear H1.
inversion_clear H.
inversion_clear H0.
rewrite H1 in H.
subst x1.
inversion_clear H2.
inversion_clear H3.
inversion_clear H.
inversion_clear H0.
rewrite H2 in H.
injection H; clear H; intros; subst x2.
exists x0; split; auto.
exists x1; split; auto.
apply semax_conseq with (And (lookup2 x e P0) P') (And P0 Q').
unfold And.
red; intros.
split; try tauto.
apply H; try tauto.
unfold And.
red; intros.
split; try tauto.
apply H0; try tauto.
apply IHsemax; auto.
(* case mutation *)
intros.
generalize P e e' H0; clear P e e' H0.
induction H; intros; try discriminate.
injection H0; clear H0; intros; subst e0 e'0.
apply semax_mutation'.
unfold And; unfold update_heap2.
red; intros.
inversion_clear H.
inversion_clear H0.
inversion_clear H1.
inversion_clear H.
inversion_clear H0.
rewrite H1 in H.
subst x0.
inversion_clear H2.
inversion_clear H3.
inversion_clear H.
inversion_clear H0.
rewrite H2 in H.
injection H; clear H; intros; subst x1.
exists x; split; auto.
exists x0; split; auto.
apply semax_conseq with (And (update_heap2 e e' P0) P') (And P0 Q').
unfold And.
red; intros.
split; try tauto.
apply H; try tauto.
unfold And.
red; intros.
split; try tauto.
apply H0; try tauto.
apply IHsemax; auto.
(* case malloc *)
intros.
generalize P x e H0; clear P x e H0.
induction H; intros; try discriminate.
injection H0; clear H0; intros; subst x0 e0.
apply semax_strengthen_pre with 
  (fun s h => forall n, (nat_e n |-> e -* update_store2 x (nat_e n) (And P0 P)) s h).
unfold And; unfold update_store2.
red; intros.
inversion_clear H.
red; intros.
generalize (H0 n); clear H0; intro.
generalize (H1 n); clear H1; intro.
red in H0.
red in H1.
split.
apply H0 with h'; auto.
apply H1 with h'; auto.
apply semax_malloc.
apply semax_conseq with 
  (And (fun s h => forall n, (nat_e n |-> e -* update_store2 x (nat_e n) P0) s h) P')
  (And P0 Q').
unfold And.
red; intros.
split; try tauto.
apply H; try tauto.
unfold And.
red; intros.
split; try tauto.
apply H0; try tauto.
apply IHsemax; auto.
(* case free *)
intros.
generalize P e H0; clear P e H0.
induction H; intros; try discriminate.
injection H0; clear H0; intros; subst e0.
apply semax_strengthen_pre with (fun s h => 
      exists l, val2loc (eval e s) = l /\
	exists v, heap.lookup l h = Some v /\
	  (And P0 P) s (h --- l)).
unfold And.
red; intros.
inversion_clear H.
inversion_clear H0.
inversion_clear H1.
inversion_clear H.
inversion_clear H0.
rewrite H1 in H.
subst x0.
inversion_clear H2.
inversion_clear H3.
inversion_clear H.
inversion_clear H0.
rewrite H2 in H.
injection H; clear H; intros; subst x1.
exists x; split; auto.
exists x0; split; auto.
apply semax_free.
apply semax_conseq with 
  (And (fun s h =>
        exists l,
          val2loc (eval e s) = l /\
          (exists v0 : heap.v, heap.lookup l h = Some v0 /\ P0 s (h --- l))) P')
  (And P0 Q').
unfold And.
red; intros.
split; try tauto.
apply H; try tauto.
unfold And.
red; intros.
split; try tauto.
apply H0; try tauto.
apply IHsemax; auto.
(* case seq *)
intros.
induction H1; intros; try discriminate.
injection H2; clear H2; intros; subst c0 d0.
clear IHsemax3 IHsemax4.
apply semax_seq with (And Q Q0).
eapply IHsemax1.
apply H1_.
auto.
eapply IHsemax2.
apply H1_0.
auto.
apply semax_conseq with (And P P') (And R Q').
unfold And; red; intros.
intuition.
unfold And; red; intros.
intuition.
apply IHsemax; auto.
(* case while *)
intros.
induction H0; intros; try discriminate.
injection H1; clear H1; intros; subst b0 c0.
clear IHsemax0.
apply semax_weaken_post with (fun s h => (And P P0) s h /\ eval_b b s = false).
unfold And; red; intros.
intuition.
apply semax_while.
apply semax_strengthen_pre with (And (fun s h => P s h /\ eval_b b s = true) 
  (fun s h => P0 s h /\ eval_b b s = true)).
unfold And; red; intros.
intuition.
apply IHsemax with c; auto.
apply semax_conseq with (And P P') (And (fun s h => P s h /\ eval_b b s = false) Q').
unfold And; red; intros; intuition.
unfold And; red; intros; intuition.
apply IHsemax0; auto.
(* case conseq *)
intros.
apply semax_conseq with (And P' P'0) (And Q' Q'0).
unfold And; red; intros; intuition.
unfold And; red; intros; intuition.
apply IHsemax with d; auto.
(* case ifte *)
intros.
induction H1; intros; try discriminate.
apply semax_conseq with (And P P') (And Q Q').
unfold And; red; intros; intuition.
unfold And; red; intros; intuition.
apply IHsemax.
auto.
clear IHsemax3 IHsemax4.
injection H2; clear H2; intros; subst b0 c0 d0.
apply semax_ifte.
apply semax_strengthen_pre with (And (fun s h => P s h /\ eval_b b s = true) 
  (fun s h => P0 s h /\ eval_b b s = true)
).
unfold And; red; intros; intuition.
eapply IHsemax1 with c; auto.
apply semax_strengthen_pre with (And (fun s h => P s h /\ eval_b b s = false) 
  (fun s h => P0 s h /\ eval_b b s = false)
).
unfold And; red; intros; intuition.
eapply IHsemax2 with d; auto.
Qed.

Lemma semax_and : forall c P Q P' Q', 
  {{ P }} c {{ Q }} -> 
  {{ P' }} c {{ Q' }} ->
  {{ And P P' }} c {{ And Q Q' }}.
intros.
apply semax_and' with c; auto.
Qed.

Lemma forward_reasoning : forall x e P,
  inde (x::nil) P ->
  ~ In x (expr_var e) ->
  {{ P }} x <- e {{ fun s h => P s h /\ eval (var_e x) s = eval e s }}.
intros.
apply semax_strengthen_pre with (
 fun s h => P s h /\ (exists v, eval (var_e x) s = v)
).
intros.
split.
auto.
exists (eval (var_e x) s).
auto.
apply semax_strengthen_pre with (
update_store2 x e
(fun s h => (P s h) /\ (eval (var_e x) s = eval e s))
).
intros.
red.
split.
red in H.
assert (In x (x::nil)).
simpl.
left; auto.
generalize (H s h x (eval e s) H2); intro X; inversion_clear X.
inversion_clear H1.
apply H3; auto.
inversion_clear H1.
inversion_clear H3.
simpl.
rewrite store.lookup_update'; auto.
auto.
apply inde_expr with (x::nil).
red; simpl; split; intros.
inversion_clear H3.
inversion_clear H5.
subst x1.
auto.
auto.
contradiction.
simpl; auto.
apply semax_assign.
Qed.

Lemma frame_rule': forall P c Q,
  {{ P }} c {{ Q }} ->
  forall R1 R2,
    inde (modified_cmd_var c) R1 -> 
    (R1 ==> R2) ->
    {{ P ** R1 }} c {{ Q ** R2 }}.
intros.
apply semax_weaken_post with (Q**R1).
red; intros.
inversion_clear H2.
inversion_clear H3.
inversion_clear H2.
inversion_clear H4.
inversion_clear H5.
red.
exists x; exists x0.
auto.
apply frame_rule.
auto.
auto.
Qed.

Lemma frame_rule'': forall c1 c2 P1 P2 Q1 Q2,
  {{ P1 }} c1 {{ Q1 }} ->
  {{ P2 }} c2 {{ Q2 }} ->    
  inde (modified_cmd_var c1) P2 ->
  inde (modified_cmd_var c2) Q1 ->
  {{ P1 ** P2 }} c1 ; c2 {{ Q1 ** Q2 }}.
intros.
generalize (frame_rule P1 c1 Q1 H P2 H1); intro.
generalize (frame_rule P2 c2 Q2 H0 Q1 H2); intro.
assert ((Q1 ** P2) ==> (P2 ** Q1)).
apply sep.con_com.
assert ((Q2 ** Q1) ==> (Q1 ** Q2)).
apply sep.con_com.
apply semax_seq with (P2 ** Q1).
apply semax_weaken_post with (Q1 ** P2).
auto.
auto.
apply semax_weaken_post with (Q2 ** Q1).
auto.
auto.
Qed.

Lemma semax_mutation_frame_rule : forall  x v c P Q v',
  {{ P }} c {{ Q }} -> 
  inde (modified_cmd_var c) (x |-> v) ->
  {{ (x |-> v') ** P }} x *<- v ; c {{ (x |-> v) ** Q }}.
intros.
apply semax_seq with ((x |-> v) ** P).
apply semax_mutation_global_alternative.
apply semax_strengthen_pre with (P ** (x |-> v)).
red; intros; rewrite sep.con_com_equiv; auto.
apply semax_weaken_post with (Q ** (x |-> v)).
red; intros; rewrite sep.con_com_equiv; auto.
apply frame_rule.
auto.
auto.
Qed.

(* 
 * definitions of arrays (contiguous areas of memory) and their properties 
 *)

Fixpoint Array (p:loc) (size:nat) {struct size} : assert :=
  match size with
    O => sep.emp
    | S n => (fun s h => exists y, (nat_e p |-> int_e y) s h) ** 
      Array (p + 1) n
  end.

Lemma Array_inde_store : forall m n s h,
  Array n m s h -> forall s', Array n m s' h.
induction m.
simpl.
auto.
simpl.
intros.
inversion_clear H.
inversion_clear H0.
decompose [and] H; clear H.
exists x.
exists x0.
split; auto.
split; auto.
split; auto.
apply IHm with s; auto.
Qed.

Ltac Array_equiv := 
  match goal with
    | id: Array ?adr1 ?size1 ?s1 ?h |-  Array ?adr2 ?size2 ?s2 ?h =>
      assert (Array_equivA1: adr2 = adr1); [omega |
        assert (Array_equivA2: size2 = size1); [omega |
          ((rewrite Array_equivA1) || idtac); ((rewrite  Array_equivA2) || idtac);
          eapply (Array_inde_store); apply id
        ]
      ]
  end.

Lemma Array_inde: forall l adr size,
  inde l (Array adr size).
induction l.
red.
simpl.
tauto.
red.
intros.
simpl in H; inversion_clear H.
subst a.
red.
split.
intros.
eapply Array_inde_store.
apply H.
intros.
eapply Array_inde_store.
apply H.
red in IHl.
apply IHl.
auto.
Qed.

Lemma Array_inde_list: forall l st sz,
  inde l (Array st sz).
  induction l.
  intros; red; simpl.
  intuition.
  simpl; intros.
  red; intros.
  simpl in H; inversion_clear H.
  split.
  intros.
  eapply Array_inde_store.
  apply H.
  intros.
  eapply Array_inde_store.
  apply H.
  red in IHl.
  eapply IHl.
  auto.
Qed.

Lemma Array_concat_split: forall size1 size2 adr,
  Array adr (size1+size2) <==> (Array adr size1 ** Array (adr+size1) size2).
  induction size1.
  split.
  intros.
  exists heap.emp; exists h.
  split.
  Disjoint_heap.
  split.
  Equal_heap.
  split.
  simpl.
  red.
  auto.
  assert (adr + 0 = adr).
  intuition.
  assert (0 +size2 = size2).
  intuition.
  rewrite H0; rewrite <- H1; auto.
  intro.
  inversion_clear H.
  inversion_clear H0.
  decompose [and] H; clear H.
  simpl in H1.
  red in H1.
  assert (adr + 0 = adr).
  intuition.
  assert (0 +size2 = size2).
  intuition.
  rewrite <- H; rewrite H3. 
  assert (h = x0).
  Heap_emp_clean.
  Equal_heap.
  rewrite H5.
  auto.
  split.
  intros.
  simpl.
  simpl in H.
  inversion_clear H.
  inversion_clear H0.
  decompose [and] H; clear H.
  inversion_clear H1.
  generalize (IHsize1 size2 (adr + 1) s x0); intro X; inversion_clear X.
  generalize (H1 H4); clear H1 H3; intros.
  inversion_clear H1.
  inversion_clear H3.
  decompose [and] H1; clear H1.
  exists (heap.union x x2); exists x3.
  split.
  Disjoint_heap.
  split.
  Equal_heap.
  split.
  exists x; exists x2.
  split.
  Disjoint_heap.
  split.
  Equal_heap.
  split.
  exists x1.
  auto.
  auto.
  assert (adr + 1 + size1 = adr + S size1).
  intuition.
  rewrite <- H1.
  auto.
  intros.
  inversion_clear H.
  inversion_clear H0.
  decompose [and] H; clear H.
  simpl.
  simpl in H1.
  inversion_clear H1.
  inversion_clear H.
  decompose [and] H1; clear H1.
  inversion_clear H3.
  exists (x1); exists (heap.union x0 x2).
  split.
  Disjoint_heap.
  split.
  Equal_heap.
  split.
  exists x3.
  auto.
  generalize (IHsize1 size2 (adr + 1) s (x0 +++ x2)); intro X; inversion_clear X.
  apply H6; clear H6 H3; intros.
  exists x2; exists x0.
  split.
  Disjoint_heap.
  split.
  Equal_heap.
  split.
  auto.
  cutrewrite (adr + 1 + size1 = adr + S size1).
  auto.
  omega.
Qed.

Ltac TArray_concat_split_r size1 size2:=
  match goal with 
    | |- Array ?adr ?size ?s ?h =>
      generalize (Array_concat_split size1 size2 adr s h); intro TArray_concat_split_rH1; inversion_clear TArray_concat_split_rH1 as [TArray_concat_split_rH11 TArray_concat_split_rH12];
        assert (TArray_concat_split_rA1: size1 + size2 = size); [omega | (rewrite <- TArray_concat_split_rA1 || idtac); clear TArray_concat_split_rA1; apply TArray_concat_split_rH12; clear TArray_concat_split_rH11 TArray_concat_split_rH12]
  end.


Ltac TArray_concat_split_l_l sz id:=
  match goal with 
    | id: Array ?adr ?size ?s ?h |- _ =>
      assert (TArray_concat_split_l_lA1: size = sz + (size - sz)); 
        [omega | 
          rewrite TArray_concat_split_l_lA1 in id; clear TArray_concat_split_l_lA1;
            generalize (Array_concat_split sz (size - sz) adr s h); intro TArray_concat_split_l_lH1;
              inversion_clear TArray_concat_split_l_lH1 as [TArray_concat_split_l_lH2 TArray_concat_split_l_lH3]; generalize (TArray_concat_split_l_lH2 id); clear TArray_concat_split_l_lH3; clear TArray_concat_split_l_lH2; intro
        ]
  end.

Ltac TArray_concat_split_l_r sz id:=
  match goal with 
    | id: Array ?adr ?size ?s ?h |- _ =>
      assert (TArray_concat_split_l_lA1: size = (size - sz) + sz); 
        [omega | 
          rewrite TArray_concat_split_l_lA1 in id; clear TArray_concat_split_l_lA1;
            generalize (Array_concat_split (size - sz) sz adr s h); intro TArray_concat_split_l_lH1;
              inversion_clear TArray_concat_split_l_lH1 as [TArray_concat_split_l_lH2 TArray_concat_split_l_lH3]; generalize (TArray_concat_split_l_lH2 id); clear TArray_concat_split_l_lH3; clear TArray_concat_split_l_lH2; intro
        ]
  end.

(* test *)
Lemma Array_split : forall size' size,
  size' <= size -> 
  forall adr s h, adr > 0 -> Array adr size s h -> 
    (Array adr size' ** Array (adr+size') (size - size')) s h.
  intros.
  TArray_concat_split_l_l size' H1.
  auto.
Qed.

Lemma Array_disjoint : forall size adr s h, adr > 0 ->
  Array adr size s h ->
  forall adr', 
    adr' >= adr+size ->
    forall z,
      h # (heap.singleton adr' z).
induction size.
simpl.
intros.
red in H0.
subst h.
apply heap.disjoint_com.
apply heap.disjoint_emp.
intros.
simpl in H0.
inversion_clear H0.
inversion_clear H2.
decompose [and] H0; clear H0.
assert (adr + 1> 0).
omega.
assert (adr' >= (adr + 1) + size).
omega.
generalize (IHsize _ _ _ H0 H6 adr' H5); intros.
apply heap.disjoint_com.
rewrite H4.
apply heap.disjoint_union.
split.
inversion_clear H3.
inversion_clear H8.
simpl in H3.
inversion_clear H3.
rewrite Z_of_nat2loc in H8.
injection H8; clear H8; intros; subst x2.
rewrite H9.
apply heap.disjoint_singleton.
omega.
auto.
apply heap.disjoint_com.
auto.
Qed.

Lemma Array_concat : forall size adr s h, adr > 0 ->
  Array adr size s h ->
  forall z, 
    Array adr (size + 1) s (h +++ (heap.singleton (adr+size) z)).
induction size.
intros.
red in H0.
red in H0.
exists (heap.singleton (adr + 0) z).
exists heap.emp.
split.
apply heap.disjoint_emp.
split.
Heap_emp_clean.
Equal_heap.
split.
exists z.
red.
exists adr.
simpl.
rewrite Z_of_nat2loc.
split; auto.
assert (adr + 0 = adr).
omega.
rewrite H1; auto.
auto.
red.
red; auto.
intros.
simpl in H0.
inversion_clear H0.
inversion_clear H1.
decompose [and] H0; clear H0.
assert ((adr + 1) > 0).
omega.
pattern (S size).
rewrite plus_n_O.
rewrite plus_Snm_nSm.
TArray_concat_split_r 1 (size + 1).
generalize (IHsize _ _ _ H0 H5 z); clear H0; intros.
inversion_clear H2.
exists x.
exists (heap.union x0 (heap.singleton ((adr + 1) + size) z)).
split.
apply heap.disjoint_union.
split; auto.
inversion_clear H4.
simpl in H2.
inversion_clear H2.
apply heap.disjoint_com.
rewrite H6.
rewrite Z_of_nat2loc in H4.
injection H4; clear H4; intros; subst x2.
apply heap.disjoint_singleton.
omega.
auto.
split.
assert (adr +  (size + 1) = (adr + 1) + size).
omega.
rewrite H2; clear H2.
Equal_heap.
split.
inversion_clear H4.
simpl in H2.
inversion_clear H2.
rewrite Z_of_nat2loc in H4.
injection H4; clear H4; intros; subst x2.
simpl.
Compose_sepcon x heap.emp.
exists x1.
red.
simpl.
exists adr.
split.
apply Z_of_nat2loc.
auto.
red; auto.
auto.
Qed.

Lemma mapstos_to_array: forall l x x' sz s h,
   (x |--> l) s h ->
   eval x s = Z_of_nat x' ->
   sz = length l ->
   Array x' sz s h.
induction l.
simpl.
intros.
subst sz.
simpl.
trivial.
simpl.
intros.
Decompose_sepcon H h1 h2.
subst sz.
Compose_sepcon h1 h2.
exists (eval a s).
eapply mapsto_equiv.
apply H2.
simpl.
auto.
simpl.
auto.
eapply IHl.
apply H5.
simpl.
rewrite H0.
rewrite inj_plus.
trivial.
auto.
Qed.

(* Definition of intialized arrays *)
Fixpoint ArrayI (x:loc) (l:list Z) {struct l} : assert :=
  match l with
    nil => sep.emp
    | hd::tl => 
      (fun s h => (nat_e x |-> int_e hd) s h) ** 
      ArrayI (x + 1) tl
  end.

Lemma ArrayI_inde_store: forall l n s h,
  ArrayI n l s h -> forall s', ArrayI n l s' h.
induction l.
simpl.
intros.
red in H.
red.
auto.
intros.
simpl in H.
Decompose_sepcon H h1 h2.
simpl.
Compose_sepcon h1 h2.
eapply mapsto_equiv'.
apply H0.
auto.
auto.
eapply IHl.
apply H3.
Qed.

Lemma ArrayI_disjoint_heap: forall lst a h' e e' s h,
  ArrayI a lst s h ->
  (nat_e e |-> e') s h' ->
  (e < a \/ e >= a + length lst) ->
  h # h'.
induction lst.
simpl.
intros.
red in H.
rewrite H.
apply heap.disjoint_com.
apply heap.disjoint_emp.
intros.
inversion_clear H1.

destruct a0.
inversion H2.
simpl in H.
inversion_clear H0.
inversion_clear H1.
simpl in H0.
rewrite Z_of_nat2loc in H0.
subst x.
inversion_clear H.
inversion_clear H0.
decompose [and] H; clear H.
inversion_clear H1.
inversion_clear H.
simpl in H1.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ in H1.
subst x1.
simpl in H5.
rewrite H4.
apply heap.disjoint_com.
apply heap.disjoint_union.
split.
rewrite H3; rewrite H5.
apply heap.disjoint_singleton.
omega.
apply heap.disjoint_com.
eapply IHlst.
apply H6.
exists e.
split.
simpl.
apply Z_of_nat2loc.
apply H3.
omega.

inversion_clear H0.
simpl in H1.
rewrite Z_of_nat2loc in H1.
inversion_clear H1.
subst x.

destruct a0.
simpl in H.
inversion_clear H.
inversion_clear H0.
decompose [and] H; clear H.
inversion_clear H1.
simpl in H.
inversion_clear H.
subst x1.
rewrite H4.
apply heap.disjoint_com.
apply heap.disjoint_union.
split.
rewrite H3; rewrite H5.
apply heap.disjoint_singleton.
simpl in H2.
intro.
subst e.
inversion_clear H2.
apply heap.disjoint_com.
eapply IHlst.
apply H6.
exists e.
simpl.
rewrite Z_of_nat2loc.
split.
reflexivity.
apply H3.
simpl in H2.
omega.

simpl in H.
inversion_clear H.
inversion_clear H0.
decompose [and] H; clear H.
inversion_clear H1.
simpl in H.
inversion_clear H.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ in H1.
subst x1.
rewrite H4.
apply heap.disjoint_com.
apply heap.disjoint_union.
split.
rewrite H3; rewrite H5.
apply heap.disjoint_singleton.
simpl in H2.
omega.
apply heap.disjoint_com.
eapply IHlst.
apply H6.
exists e.
simpl.
rewrite Z_of_nat2loc.
split.
reflexivity.
apply H3.
simpl.
simpl in H2.
omega.
Qed.

(*Lemma ArrayI_disjoint_heap: forall lx x h' e1 x1 s h,
  ArrayI x lx s h ->
  (e1 |-> x1) s h' ->
  ((eval e1 s < eval (nat_e x) s)%Z \/ (eval e1 s >= eval (nat_e (x + length lx)) s)%Z) ->
  h # h'.
induction lx.
do 6 intro.
intros.
simpl in H.
red in H.
rewrite H.
Disjoint_heap.
simpl.
do 6 intro.
intros.
Decompose_sepcon H h1 h2.
eapply heap.disjoint_com.
rewrite H3.
eapply heap.disjoint_union.
split.
red in H2.
inversion_clear H2.
simpl in H4.
inversion_clear H4.
rewrite H6.
red in H0.
inversion_clear H0.
inversion_clear H4.
eapply heap.disjoint_com.
rewrite H7.
eapply heap.disjoint_singleton.
inversion_clear H1.
red; intros.
subst x2.
subst x0.
generalize (val2loc_injection _ _ H1); clear H1; intro.
rewrite H0 in H4.
assert (forall x, ~(x < x)%Z).
intuition.
intuition.
auto.
red; intro.
subst x2.
subst x0.
generalize (val2loc_injection _ _ H1); clear H1; intro.
rewrite <-H0 in H4.
rewrite inj_plus in H4.
assert (S (length lx) = length lx + 1).
intuition.
rewrite H1 in H4.
assert (forall x y, y > 0 -> ~(Z_of_nat x >= (Z_of_nat x) + (Z_of_nat y))%Z).
intuition.
red in H2.
eapply H2.
assert (length lx + 1 > 0).
omega.
apply H8.
apply H4.
apply heap.disjoint_com.
apply (IHlx (x+1) h' e1 x1 s h2 H5 H0).
inversion_clear H1.
left.
simpl.
rewrite inj_plus.
intuition.
right.
simpl.
rewrite inj_plus.
rewrite inj_plus.
rewrite inj_plus in H4.
assert (S (length lx) = length lx + 1).
intuition.
rewrite H1 in H4.
clear H1.
rewrite inj_plus in H4.
intuition.
Qed.*)


Lemma Data_destructive_update_inv2: forall lx x h1 h2 e1 x1 s h,
  (ArrayI x lx ** TT) s h ->
  h1 # h2 ->
  h = h1 +++ h2 ->
  (nat_e e1 |-> x1) s h1 ->
  (e1 < x \/ e1 >= x + length lx) ->
  (ArrayI x lx ** TT) s h2.
do 8 intro.
intros.
Decompose_sepcon H h'1 h'2.
generalize (ArrayI_disjoint_heap lx x h1 e1 x1 s h'1 H4 H2 H3); intros.
assert (h'1 +++ h'2 = h1 +++ h2).
rewrite <-H5.
auto.
generalize (heap.disjoint_comp h'1 h1 h2 h'2 (heap.disjoint_com _ _ H6) H0 H H8); intro H9.
inversion_clear H9.
inversion_clear H10.
Compose_sepcon h'1 x0.
auto.
red; auto.
Qed.

(*Lemma Data_destructive_update_inv2: forall lx x h1 h2 e1 x1 s h,
  (ArrayI x lx ** TT) s h ->
  h1 # h2 ->
  h = h1 +++ h2 ->
  (e1 |-> x1) s h1 ->
  ((eval e1 s < eval (nat_e x) s)%Z \/ (eval e1 s >= eval (nat_e (x + length lx)) s)%Z) ->
  (ArrayI x lx ** TT) s h2.*)

Lemma Data_destructive_update_inv: forall lx x h1 h2 e1 x1 x2 h'1 h' s h,
  (ArrayI x lx ** TT) s h ->
  h1 # h2 ->
  h = h1 +++ h2 ->
  (nat_e e1 |-> x1) s h1 ->
  (nat_e e1 |-> x2) s h'1 ->
  h'1 # h2 ->
  h' = h'1 +++ h2 ->
  (e1 < x \/ e1 >= x + length lx) ->
  (ArrayI x lx ** TT) s h'.
do 11 intro.
intros.
generalize (Data_destructive_update_inv2 lx x h1 h2 e1 x1 s h H H0 H1 H2 H6); intros.
Decompose_sepcon H7 h21 h22.
Compose_sepcon h21 (h22 +++ h'1).
auto.
red; auto.
Qed.

(*Lemma Data_destructive_update_inv: forall lx x h1 h2 e1 x1 x2 h'1 h' s h,
  (ArrayI x lx ** TT) s h ->
  h1 # h2 ->
  h = h1 +++ h2 ->
  (e1 |-> x1) s h1 ->
  (e1 |-> x2) s h'1 ->
  h'1 # h2 ->
  h' = h'1 +++ h2 ->
  ((eval e1 s < eval (nat_e x) s)%Z \/ (eval e1 s >= eval (nat_e (x + length lx)) s)%Z) ->
  (ArrayI x lx ** TT) s h'.*)

