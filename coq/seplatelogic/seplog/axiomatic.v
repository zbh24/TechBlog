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

(* commands of the langage *)

Inductive cmd : Set :=
  skip : cmd
  | assign : var.v -> expr -> cmd
  | lookup : var.v -> expr -> cmd
  | mutation : expr -> expr -> cmd
  | malloc : var.v -> expr -> cmd
  | free : expr -> cmd
  | while : expr_b -> cmd -> cmd
  | seq : cmd -> cmd -> cmd
  | ifte : expr_b -> cmd -> cmd -> cmd.

Notation "x <- e" := (assign x e) (at level 80) : sep_scope.
Notation "x '<-*' e" := (lookup x e) (at level 80) : sep_scope.
Notation "e '*<-' f" := (mutation e f) (at level 80) : sep_scope.
Notation "x '<-malloc' e" := (malloc x e) (at level 80) : sep_scope.
Notation "c ; d" := (seq c d) (at level 81, right associativity) : sep_scope.
Notation "'ifte' a 'thendo' x 'elsedo' y" := (ifte a x y)(at level 80) : sep_scope.

Open Local Scope sep_scope.
Open Local Scope heap_scope.

(* states *)

Close Local Scope nat_scope.

Definition state := prod store.s heap.h. 

Open Local Scope nat_scope.

(******************************************************************************)

(** operational semantics *)

Inductive exec : option state -> cmd -> option state -> Prop :=
  exec_none : forall c, exec None c None
    
  | exec_skip:  forall s h,  exec (Some (s, h)) skip (Some (s, h))
    
  | exec_assign : forall s h x e,
    exec (Some (s, h)) (x <- e) (Some (store.update x (eval e s) s, h))
    
  | exec_lookup : forall s h x e p v,
    val2loc (eval e s) = p -> (* the relative integer is cast to a location *)
    heap.lookup p h = Some v -> (* we extract the corresponding cell contents if any *)
    exec (Some (s, h)) (x <-* e) (Some (store.update x v s, h))

  | exec_lookup_err : forall s h x e p,
    val2loc (eval e s) = p -> 
    heap.lookup p h = None -> (* the corresponding location is not allocated *)
    exec (Some (s, h)) (x <-* e) None
    
  | exec_mutation : forall s h e e' p v,
    val2loc (eval e s) = p -> (* compute the address *)
    heap.lookup p h = Some v -> (* extract the value (if ever present) *)
    exec (Some (s, h)) (e *<- e') (Some (s, heap.update p (eval e' s) h))
    
  | exec_mutation_err : forall s h e e' p,
    val2loc (eval e s) = p -> (* compute the address *)
    heap.lookup p h = None -> (* if the address is not allocated... *)
    exec (Some (s, h)) (e *<- e') None

  | exec_malloc : forall s h x e n,
    h # heap.singleton n (eval e s) ->
    exec (Some (s, h)) (x <-malloc e) 
    (Some (store.update x (Z_of_nat n) s, h +++ (heap.singleton n (eval e s))))

  | exec_free : forall s h e v p,
    val2loc (eval e s) = p ->
    heap.lookup p h = Some v->
    exec (Some (s, h)) (free e) (Some (s, h --- p))

  | exec_free_err : forall s h e p,
    val2loc (eval e s) = p -> (* compute the address *)
    heap.lookup p h = None -> (* if the address is not allocated *)
    exec (Some (s, h)) (free e) None
    
  | exec_seq : forall s s' s'' c d,
    exec s c s' -> exec s' d s'' -> exec s (c ; d) s''
    
  | exec_while_true : forall s h s' s'' b c,
    eval_b b s = true ->
    exec (Some (s, h)) c s' ->
    exec s' (while b c) s'' ->
    exec (Some (s, h)) (while b c) s''
    
  | exec_while_false : forall s h b c,
    eval_b b s = false ->
    exec (Some (s, h)) (while b c) (Some (s, h))
    
  | exec_ifte_true : forall b c d s h s',
    eval_b b s = true ->
    exec (Some (s, h)) c s' ->
    exec (Some (s, h)) (ifte b thendo c elsedo d) s'
    
  | exec_ifte_false : forall b c d s h s',
    eval_b b s = false ->
    exec (Some (s, h)) d s' ->
    exec (Some (s, h)) (ifte b thendo c elsedo d) s'.

Notation "s -- c --> t" := (exec s c t) (at level 82) : sep_scope.

Lemma from_none' : forall s0 c s, (s0 -- c --> s) -> s0 = None -> s = None.
  do 4 intro.
  induction H; intro; try auto||discriminate.
Qed.

Lemma from_none : forall c s, (None -- c --> s) -> s = None.
  intros; eapply from_none'.
  apply H.
  auto.
Qed.

(* Axiomatic Semantics *)

(* update the store used in an assertion using the value of an expr *)
Definition update_store2 (x:var.v) (e:expr) (P:assert) : assert :=
  fun s h => P (store.update x (eval e s) s) h.

(* update the store used in an assertion using the value held in a heap *)
Definition lookup2 (x:var.v) (e:expr) (P:assert) : assert :=
  fun s h =>
    exists p, val2loc (eval e s) = p /\
      exists z, heap.lookup p h = Some z /\
	P (store.update x z s) h.

(* update the heap used in an assertion *)
Definition update_heap2 (e:expr) (e':expr) (P:assert) : assert :=
  fun s h =>
    exists p, val2loc (eval e s) = p /\
      exists z, heap.lookup p h = Some z /\
	P s (heap.update p (eval e' s) h).

Inductive semax : assert -> cmd -> assert -> Prop :=
  semax_skip: forall P, semax P skip P
  | semax_assign : forall P x e, 
    semax (update_store2 x e P) (x <- e) P
  | semax_lookup : forall P x e,
    semax (lookup2 x e P) (x <-* e) P
  | semax_mutation : forall P e e',
    semax (update_heap2 e e' P) (e *<- e') P
  | semax_malloc : forall P x e,
    semax (fun s h => forall n, ((nat_e n)|->e -* update_store2 x (nat_e n) P) s h)
    (x <-malloc e) P
  | semax_free : forall P e,
    semax 
    (fun s h => 
      exists l, val2loc (eval e s) = l /\
	exists v, heap.lookup l h = Some v /\
	  P s (h --- l))
    (free e)
    P
  | semax_seq : forall P Q R c d, 
    semax P c Q -> semax Q d R -> semax P (c ; d) R
  | semax_while : forall P b c, 
    semax (fun s h => (P s h /\ eval_b b s = true)) c P -> 
    semax P (while b c) (fun s h => P s h /\ eval_b b s = false)
  | semax_conseq : forall (P P' Q Q':assert) c,
    (Q' ==> Q) -> (P ==> P') -> 
    semax P' c Q' -> semax P c Q
  | semax_ifte : forall P Q b c d,
    semax (fun s h => P s h /\ eval_b b s = true) c Q ->
    semax (fun s h => P s h /\ eval_b b s = false) d Q ->
    semax P (ifte b thendo c elsedo d) Q.

Notation "{{ P }} c {{ Q }}" := (semax P c Q) (at level 82) : sep_scope.

(** axiomatic semantic lemmas *)

Lemma semax_weaken_post : forall P (Q Q':assert) c,
  (Q' ==> Q) -> {{ P }} c {{ Q' }} -> {{ P }} c {{ Q }}.
  intros.
  apply semax_conseq with (P':=P) (Q':=Q').
  auto.
  red; auto.
  auto.
Qed.

Lemma semax_strengthen_pre : forall (P P':assert) Q c,
  (P ==> P') -> {{ P' }} c {{ Q }} -> {{ P }} c {{ Q }}.
  intros.
  apply semax_conseq with (P':=P') (Q':=Q).
  red; auto.
  auto.
  auto.
Qed.

(* Definition of axiomatic semantic linked to the operationnal semantic *)

Definition semax' (P:assert) (c:cmd) (Q:assert) : Prop :=
    forall s h, (P s h -> ~(Some (s, h) -- c --> None)) /\
      (forall s' h', P s h -> (Some (s, h) -- c --> Some (s', h')) -> Q s' h').

Lemma semax_sound : forall P Q c,
  {{ P }} c {{ Q }} -> semax' P c Q.
  intros.
  induction H.
  (*
   * case skip
   *)
  red.
  intros.
  split.
  intros.
  red.
  intro.
  inversion H0.
  intros.
  inversion H0.
  subst s' h'.
  auto.
  (*
   * case semax_assign_var_e
   *)
  red.
  intros.
  split.
  intro.
  intro.
  inversion_clear H0.
  intros.
  inversion H0.
  subst h' s' e0 x0 h0 s0.
  unfold update_store2 in H.
  auto.
  (*
   * case semax_assign_var_lookup
   *)
  red.
  split; intros.
  intro X; inversion_clear X.
  red in H.
  inversion_clear H as [l'].
  inversion_clear H2.
  rewrite H0 in H; subst l'.
  inversion_clear H3 as [z].
  rewrite H1 in H; inversion_clear H; discriminate.
  inversion H0.
  subst h' s' s0 h0 x0 e0.
  red in H.
  inversion_clear H as [l'].
  inversion_clear H1.
  rewrite H4 in H; subst l'.
  inversion_clear H2 as [z'].
  inversion_clear H.
  rewrite H8 in H1; injection H1; clear H1; intro; subst z'; exact H2.
  (*
   * case semax_assign_lookup_expr
   *)
  red.
  split; intros.
  intro.
  inversion_clear H0.
  red in H.
  inversion_clear H as [l'].
  inversion_clear H0.
  rewrite H1 in H; subst l'.
  inversion_clear H3 as [z].
  rewrite H2 in H; inversion_clear H; discriminate.
  inversion H0.
  subst s' h' s0 h0 e0 e'0.
  red in H.
  inversion_clear H as [l'].
  inversion_clear H1.
  rewrite H4 in H; subst l'.
  inversion_clear H2 as [z'].
  exact (proj2 H).
  (*
   * case semax_malloc
   *)
  red.
  split; intros.
  intro X; inversion X.
  inversion H0.
  subst s0 h0 x0 e0 s' h'.
  generalize (H n); clear H; intro.
  unfold update_store2 in H.
  simpl in H.
  unfold sep.imp in H.
  apply H with (h':=heap.singleton n (eval e s)); auto.
  split; auto.
  exists n.
  simpl.
  split; auto.
  apply Z_of_nat2loc.
  (*
   * case semax_free
   *)
  red.
  split; intros.
  intro X; inversion X.
  subst s0 h0 e0.
  inversion_clear H as [l'].
  inversion_clear H0.
  rewrite H3 in H; subst l'.
  inversion_clear H1.
  rewrite H4 in H; inversion H; discriminate.
  inversion_clear H as [l].
  inversion_clear H1.
  inversion_clear H2.
  inversion_clear H1.
  inversion H0.
  subst s0 h0 e0 s' h'.
  rewrite H in H7; subst p.
  assumption.
  (*
   * case semax_seq
   *)
  red.
  split; intros.
  intro X; inversion_clear X.
  red in IHsemax1.
  generalize (IHsemax1 s h); intro.
  inversion_clear H4.
  destruct s'.
  destruct s0.
  generalize (H6 _ _ H1 H2); intro.
  generalize (IHsemax2 s0 h0); intro.
  inversion_clear H7.
  tauto.
  tauto.
  inversion_clear H2.
  red in IHsemax1.
  red in IHsemax2.
  destruct s'0.
  destruct s0 as [s'' h''].
  generalize (IHsemax1 s h); intro.
  inversion_clear H2.
  generalize (H6 _ _ H1 H3); intro.
  generalize (IHsemax2 s'' h''); intro.
  inversion_clear H7.
  apply (H9 _ _ H2 H4).
  generalize (from_none _ _ H4); intro.
  discriminate.
  (*
   * case semax_while
   *)
  red.
  split; intros.
  intro.
  assert (exists d, d = while b c).
  exists (while b c); auto.
  inversion_clear H2.
  rewrite <-H3 in H1.
  assert (exists S, S = Some (s, h)).
  exists (Some (s, h)); auto.
  inversion_clear H2.
  rewrite <-H4 in H1.
  generalize P b c H IHsemax s h H0 H3 H4;
    clear P b c H IHsemax s h H0 H3 H4.
  rename x into C.
  rename x0 into st0.
  assert (exists S, S = @None state).
  exists (@None state); auto.
  inversion_clear H.
  rewrite <-H0 in H1.
  generalize H0; clear H0.
  rename x into st'.
  induction H1; intros; try discriminate.
  injection H4; clear H4; intros; subst s0 h0.
  injection H3; clear H3; intros; subst b0 c0.
  red in IHsemax.
  generalize (IHsemax s h); intro.
  inversion_clear H3.
  generalize (H4 (conj H2 H)); clear H4; intro.
  destruct s'.
  destruct s0.
  generalize (H5 s0 h0 (conj H2 H) H1_); clear H5; intro.
  generalize (IHexec2 H0 _ _ _ H1 IHsemax _ _ H4).
  auto.
  tauto.
  assert (exists d, d = while b c).
  exists (while b c); auto.
  inversion_clear H2 as [C].
  rewrite <-H3 in H1.
  assert (exists S, S = Some (s, h)).
  exists (Some (s, h)); auto.
  inversion_clear H2 as [sigma].
  rewrite <-H4 in H1.
  assert (exists S, S = Some (s', h')).
  exists (Some (s', h')); auto.
  inversion_clear H2 as [sigma'].
  rewrite <-H5 in H1.
  generalize P b c H IHsemax s h s' h' H0 H3 H4 H5;
    clear P b c H IHsemax s h s' h' H0 H3 H4 H5.
  induction H1; intros; try discriminate.
  (*
   * case exec_while true
   *)
  injection H3; clear H3; intros; subst c0 b0.
  injection H4; clear H4; intros; subst h0 s0.
  clear IHexec1.
  rename s'' into sigma'.
  rename s' into sigma''.
  rename s'0 into s'.
    (* we know s,h |= P /\ b, by the inductive hypothesis IHsemax we have sigma'' |= P *)
  induction sigma''.
  induction a.
  rename a into s''.
  rename b0 into h''.
  assert (P s'' h'').
  red in IHsemax.
  generalize (IHsemax s h); intro.
  inversion_clear H2.
  apply H4; auto.
  (* since sigma'' --while b c--> sigma' and {P}while b c{P /\ ~b}, then we have sigma' |= P /\ ~b *)
  generalize (IHexec2 _ _ _ H0 IHsemax _ _ s' h' H2 (refl_equal (while b c)) (refl_equal (Some (s'', h'')))); intro.
  auto.
  generalize (from_none _ _ H1_0); intro X; rewrite H5 in X; discriminate X.
  (*
   * case exec_while false 
   *)
  intros.
  injection H5; clear H5; intros; subst s' h'.
  injection H4; clear H4; intros; subst s0 h0.
  injection H3; clear H3; intros; subst b0 c0.
  auto.
  (*
   *
   *)
  red.
  split; intros.
  intro.
  red in IHsemax.
  generalize (IHsemax s h); intros.
  inversion_clear H4.
  apply H5.
  apply H0.
  auto.
  auto.
  intros.
  red in IHsemax.
  generalize (IHsemax s h);intro.
  inversion_clear H4.
  apply H.
  apply H6.
  apply H0.
  auto.
  auto.
  (*
   * ifte
   *)
  red.
  intros.
  cut ( eval_b b s = true \/ eval_b b s = false ).
  split; intros.
  intro.
  inversion_clear H3.
  red in IHsemax1.
  generalize (IHsemax1 s h); intro.
  inversion_clear H3.
  apply H6.
  auto.
  auto.
  generalize (IHsemax2 s h); intro.
  inversion_clear H3.
  apply H6.
  auto.
  auto.
  intros.
  inversion_clear H3.
  red in IHsemax1.
  generalize (IHsemax1 s h); intro.
  inversion_clear H3.
  apply H7.
  auto.
  auto.
  (* on doit prouver que "s,h -- c --> s',h'" est vrai, il suffit 
  d'inverser la derivation H3 et d'utilise le fait que (eval_b b s)=true *)
  inversion_clear H1.
  rewrite H4 in H3; discriminate H3.
  (* cas ou eval_b b s <> true, pareil que ci-dessus *)
  red in IHsemax2.
  generalize (IHsemax2 s h); intro.
  inversion_clear H1.
  apply H7.
  auto.
  auto.
  case (eval_b b s); auto.
Qed.


Definition wp_semantics (c: cmd) (Q: assert): assert :=
  fun s h =>
    ~ ((Some (s, h)) -- c --> None) /\
    forall s' h',
      (Some (s, h)) -- c --> (Some (s', h')) -> Q s' h'.

Lemma exec_lookup_not_None: forall s h v e,
  ~ (Some (s, h) -- v <-* e --> None) ->
  exists p : loc,
    val2loc (eval e s) = p /\
    (exists z : heap.v, heap.lookup p h = Some z).
  intros.
  assert ((Some (s, h) -- v <-* e --> None) \/ exists s', exists h', (Some (s, h) -- v <-* e --> Some (s',h'))).
  assert (heap.lookup (val2loc (eval e s)) h = None \/ exists z, heap.lookup (val2loc (eval e s)) h = Some z).
  intros.
  destruct (heap.lookup (val2loc (eval e s)) h); intuition.
  right; exists v0; auto.
  inversion_clear H0.
  left.
  eapply exec_lookup_err.
  intuition.
  auto.
  right.
  inversion_clear H1.  
  exists (store.update v x s); exists  h.
  eapply exec_lookup.
  intuition.
  auto.
  inversion_clear H0.
  tauto.
  inversion_clear H1.
  inversion_clear H0.
  inversion_clear H1.
  exists p; split; auto.
  exists v0; auto.
Qed.
  
Lemma exec_mutation_not_None: forall s h e e0,
  ~ (Some (s, h) -- e *<- e0 --> None) ->
  exists p : loc,
    val2loc (eval e s) = p /\
    (exists z : heap.v, heap.lookup p h = Some z).
  intros.
  assert ((Some (s, h) -- e *<- e0 --> None) \/ exists s', exists h', (Some (s, h) -- e *<- e0 --> Some (s',h'))).
  assert (heap.lookup (val2loc (eval e s)) h = None \/ exists z, heap.lookup (val2loc (eval e s)) h = Some z).
  intros.
  destruct (heap.lookup (val2loc (eval e s)) h); intuition.
  right; exists v; auto.
  inversion_clear H0.
  left.
  eapply exec_mutation_err.
  intuition.
  auto.
  right.
  inversion_clear H1.  
  exists s; exists  (heap.update (val2loc (eval e s)) (eval e0 s) h).
  eapply exec_mutation.
  auto.
  apply H0.
  inversion_clear H0.
  tauto.
  inversion_clear H1.
  inversion_clear H0.
  inversion_clear H1.
  exists p; split; auto.
  exists v; auto.
Qed.

Lemma exec_free_not_None: forall s h e,
  ~ (Some (s, h) -- free e --> None) ->
  exists p : loc,
    val2loc (eval e s) = p /\
    (exists z : heap.v, heap.lookup p h = Some z).
  intros.
  assert ((Some (s, h) -- free e --> None) \/ exists s', exists h', (Some (s, h) -- free e --> Some (s',h'))).
  assert (heap.lookup (val2loc (eval e s)) h = None \/ exists z, heap.lookup (val2loc (eval e s)) h = Some z).
  intros.
  destruct (heap.lookup (val2loc (eval e s)) h); intuition.
  right; exists v; auto.
  inversion_clear H0.
  left.
  eapply exec_free_err.
  intuition.
  auto.
  right.
  inversion_clear H1.
  exists s; exists (h --- (val2loc (eval e s))).
  eapply exec_free.
  auto.
  apply H0.
  inversion_clear H0; try tauto.
  inversion_clear H1.
  inversion_clear H0.
  inversion_clear H1.
  exists p; split; auto.
  exists v; auto.
Qed.

Lemma exec_seq1_not_None: forall s h c1 c2,
  ~ (Some (s, h) -- (c1; c2) --> None) ->
  ~ (Some (s, h) -- c1 --> None).
  intros.
  red; intros.
  assert (Some (s, h) -- c1; c2 --> None).
  eapply exec_seq.
  apply H0.
  apply exec_none.
  tauto.
Qed.
  
Lemma exec_seq2_not_None: forall s h c1 c2 s' h',
  ~ (Some (s, h) -- (c1; c2) --> None) ->
  Some (s, h) -- c1 --> Some (s',h') ->
  ~ (Some (s', h') -- c2 --> None).
  intros.
  red; intros.
  assert (Some (s, h) -- c1; c2 --> None).
  eapply exec_seq.
  apply H0.
  auto.
  tauto.
Qed.
  
Lemma exec_ifte1_not_None: forall s h c1 c2 e,
  ~ (Some (s, h) -- (ifte e thendo c1 elsedo c2) --> None) ->
  eval_b e s = true ->
  (~ (Some (s, h) -- c1 --> None)).
  intros.
  red; intros.
  assert (Some (s, h) -- ifte e thendo c1 elsedo c2 --> None).
  eapply exec_ifte_true; auto.
  tauto.
Qed.

Lemma exec_ifte2_not_None: forall s h c1 c2 e,
    ~ (Some (s, h) -- (ifte e thendo c1 elsedo c2) --> None) ->
  eval_b e s = false ->
  ~ (Some (s, h) -- c2 --> None).
  intros.
  red; intros.
  assert (Some (s, h) -- ifte e thendo c1 elsedo c2 --> None).
  eapply exec_ifte_false; auto.
  tauto.
Qed.
 
Lemma exec_while1_not_None: forall s h e c,
    ~ (Some (s, h) -- while e c --> None) ->
    eval_b e s = true ->
    ~ (Some (s, h) -- c --> None).
  intros.
  red; intros.
  assert (Some (s, h) -- while e c --> None).
  eapply exec_while_true.
  auto.
  apply H1.
  apply exec_none.
  tauto.
Qed.

Lemma exec_while2_not_None: forall s h e c s' h',
    ~ (Some (s, h) -- while e c --> None) ->
    eval_b e s = true ->
    Some (s, h) -- c --> Some (s', h') ->
   ~ (Some (s', h') -- while e c --> None).
  intros.
  red; intros.
  assert (Some (s, h) -- while e c --> None).
  eapply exec_while_true.
  auto.
  apply H1.
  apply H2.
  tauto.
Qed.


Lemma wp_semantics_sound: forall c Q,
  {{wp_semantics c Q}} c {{Q}}.
  induction c; intros.

  eapply semax_strengthen_pre with Q.
  red; intros.
  red in H.
  inversion_clear H.
  apply H1.
  apply exec_skip.
  apply semax_skip.

  eapply semax_strengthen_pre with (update_store2 v e Q).
  red; intros.
  red in H.
  red.
  inversion_clear H.
  apply H1.
  apply exec_assign.
  apply semax_assign.

  eapply semax_strengthen_pre with (lookup2 v e Q).
  red; intros.
  red in H.
  red.
  inversion_clear H.
  generalize (exec_lookup_not_None _ _ _ _ H0); intros.
  inversion_clear H.
  inversion_clear H2.
  inversion_clear H3.
  exists x; split; auto.
  exists x0; split; auto.
  apply H1.
  eapply exec_lookup.
  apply H.
  auto.
  apply semax_lookup.
  
  eapply semax_strengthen_pre with (update_heap2 e e0 Q).
  red; intros.
  red in H.
  red.
  inversion_clear H.
  generalize (exec_mutation_not_None _ _ _ _ H0); intros.
  inversion_clear H.
  inversion_clear H2.
  inversion_clear H3.
  exists x; split; auto.
  exists x0; split; auto.
  apply H1.
  eapply exec_mutation.
  apply H.
  apply H2.
  apply semax_mutation.

  eapply semax_strengthen_pre with (fun s h => forall n, ((nat_e n)|->e -* update_store2 v (nat_e n) Q) s h).
  red; intros.
  red in H.
  red.
  inversion_clear H.
  intros.
  red.
  apply H1.
  rewrite H2.
  inversion_clear H.
  red in H4.
  inversion_clear H4.
  inversion_clear H.
  rewrite H5.
  simpl.
  simpl in H4.
  rewrite Z_of_nat2loc in H4.
  subst x.  
  eapply exec_malloc.
  rewrite H5 in H3; auto.
  eapply semax_malloc.

  eapply  semax_strengthen_pre with (fun s h => exists l, val2loc (eval e s) = l /\ exists v, heap.lookup l h = Some v /\ Q s (h --- l)).
  red; intros.
  red in H.
  inversion_clear H.
  generalize (exec_free_not_None _ _ _ H0); intros.
  inversion_clear H.
  inversion_clear H2.
  inversion_clear H3.
  exists x; split; auto.
  exists x0; split; auto.
  apply H1.
  eapply exec_free.
  auto.
  apply H2.
  apply semax_free.

  eapply semax_weaken_post with (fun s' h' => (wp_semantics (while e c) Q) s' h' /\ eval_b e s' = false).
  red; intros.
  inversion_clear H.
  red in H0.
  inversion_clear H0.
  eapply H2.
  eapply exec_while_false.
  auto.
  eapply semax_while.
  eapply  semax_strengthen_pre with (wp_semantics c (wp_semantics (while e c) Q)).
  red; intros.
  inversion_clear H.
  red in H0.
  inversion_clear H0.
  red; split.
  intros.
  eapply exec_while1_not_None with e; auto.
  red.
  split.
  eapply exec_while2_not_None.
  apply H.
  auto.
  auto.
  intros.
  apply H2.
  eapply exec_while_true.
  auto.
  apply H0.
  auto.
  apply IHc.

  eapply  semax_strengthen_pre with (wp_semantics c1 (wp_semantics c2 Q)).
  red; intros.
  red in H.
  inversion_clear H.
  red; split; auto.
  eapply exec_seq1_not_None.
  apply H0.
  intros.
  red; intros.
  split.
  eapply exec_seq2_not_None.
  apply H0.
  auto.
  intros.
  eapply H1.
  eapply exec_seq.
  apply H.
  apply H2.
  eapply semax_seq; [apply IHc1 | apply IHc2].
  eapply semax_ifte.
  eapply  semax_strengthen_pre with (fun s' h' => (wp_semantics c1 Q) s' h' /\ eval_b e s' = true).
  red; intros.
  inversion_clear H.
  split; auto.
  red in H0.
  inversion_clear H0.
  red.
  split.
  eapply exec_ifte1_not_None.
  apply H.
  auto.
  intros.
  apply H2.
  eapply exec_ifte_true.
  auto.
  auto.
  
  eapply  semax_strengthen_pre with (wp_semantics c1 Q).
  red; intros; intuition.
  apply IHc1.

  eapply  semax_strengthen_pre with (fun s' h' => (wp_semantics c2 Q) s' h' /\ eval_b e s' = false).
  red; intros.
  inversion_clear H.
  split; auto.
  red in H0.
  inversion_clear H0.
  red.
  split.
  eapply exec_ifte2_not_None.
  apply H.
  auto.
  intros.
  apply H2.
  eapply exec_ifte_false.
  auto.
  auto.
  
  eapply  semax_strengthen_pre with (wp_semantics c2 Q).
  red; intros; intuition.
  apply IHc2.
Qed.

Lemma semax_complete : forall P Q c,
  semax' P c Q -> {{ P }} c {{ Q }}.
  intros.
  generalize (wp_semantics_sound c Q).
  intros.
  eapply semax_strengthen_pre with (wp_semantics c Q); auto.
  red; intros.
  red.
  generalize (H s h); clear H; intros.
  inversion_clear H.
  split.
  apply (H2 H1).
  intros; apply H3; auto.
Qed.

Definition semax_alternative (P:assert) (c:cmd) (Q:assert) : Prop :=
  forall s h, P s h ->
    (forall s' h', ((Some (s, h)) -- c --> (Some (s', h'))) -> (Q s' h')).

Lemma semax_sound_alternative : forall P Q c,
  {{ P }} c {{ Q }} -> semax_alternative P c Q.
  intros.
  generalize (semax_sound _ _ _ H); intro.
  red in H0.
  red.
  intros.
  generalize (H0 s h); intro.
  inversion_clear H3.
  auto.
Qed.

(*
 * derived Reynolds' axioms
 *)

Lemma semax_lookup_backwards : forall x e P,
  {{ fun s h => exists e0, (e|->e0 ** (e|->e0 -* update_store2 x e0 P)) s h }} x <-* e {{ P }}.
  intros.
  apply semax_strengthen_pre with (lookup2 x e P).
  do 3 intro.
  inversion_clear H.
  generalize (sep.mp _ _ _ _ H0); intro.
  red in H.
  red.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H0.
  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H2.
  inversion_clear H3.
  exists x3.
  split; auto.
  exists (eval x0 s).
  split; auto.
  rewrite H0.
  apply heap.lookup_union; auto.
  rewrite H5.
  rewrite heap.lookup_singleton; auto.
  apply semax_lookup.
Qed.

Lemma semax_lookup_backwards_alternative : forall x e P e0,
  {{ e|->e0 ** (e|->e0 -* update_store2 x e0 P) }} x <-* e {{ P }}.
  intros.
  apply semax_strengthen_pre with 
    (fun s h =>
      exists e0, (e|->e0 ** (e|->e0 -* update_store2 x e0 P)) s h).
  intros.
  exists e0.
  auto.
  apply semax_lookup_backwards.
Qed.

Lemma semax_mutation_local: forall x v v',
    {{ x |-> v }} x *<- v' {{ x |-> v' }}.
  intros.
  apply semax_conseq with (P':=update_heap2 x v' (x|->v'))
    (Q':=x|->v') (c:=mutation x  v').
  red; intros.
  intuition.
  red; intros.
  inversion_clear H.
  inversion_clear H0.
  red.
  exists x0; auto.
  split; auto.
  exists (eval v s).
  split.
  rewrite H1.
  apply heap.lookup_singleton.
  exists x0.
  split; auto.
  apply trans_eq with (heap.update x0 (eval v' s) (heap.singleton x0 (eval v s))).
  rewrite H1; auto.
  apply heap.update_singleton.
  apply semax_mutation.
Qed.

(*
 * frame rule
 *)

Fixpoint modified_cmd_var (c:cmd) {struct c} : list var.v :=
  match c with 
    skip => nil
    | x <- e => x::nil
    | x <-* e => x::nil
    | e *<- f => nil
    | x <-malloc e => x::nil
    | free e => nil
    | c1 ; c2 => modified_cmd_var c1 ++ modified_cmd_var c2
    | ifte a thendo c1 elsedo c2 => modified_cmd_var c1 ++ modified_cmd_var c2
    | while a c1 => modified_cmd_var c1
   end.

Fixpoint modified_loc_expr (c:cmd) {struct c} : list expr :=
  match c with 
    skip => nil
    | x <- e => nil
    | x <-* e => nil
    | e *<- f => e::nil
    | x <-malloc e => nil
    | free e => e::nil
    | c1 ; c2 => modified_loc_expr c1 ++ modified_loc_expr c2
    | ifte a thendo c1 elsedo c2 => modified_loc_expr c1 ++ modified_loc_expr c2
    | while a c1 => modified_loc_expr c1
  end.

Lemma inde_seq : forall R c d,
  inde (modified_cmd_var (c; d)) R ->
  inde (modified_cmd_var c) R /\ inde (modified_cmd_var d) R.
intros.
split.
red.
intros.  
split; intro.
red in H.
generalize (H s h x v); intro.
assert (In x (modified_cmd_var (c; d))).
simpl.
apply in_or_app.
auto.
tauto.
red in H.
generalize (H s h x v); intros.
assert (In x (modified_cmd_var (c; d))).
simpl.
apply in_or_app.
auto.
tauto.
red.
intros.  
split; intro.
red in H.
generalize (H s h x v); intro.
assert (In x (modified_cmd_var (c; d))).
simpl.
apply in_or_app.
auto.
tauto.
red in H.
generalize (H s h x v); intros.
assert (In x (modified_cmd_var (c; d))).
simpl.
apply in_or_app.
auto.
tauto.
Qed.

Lemma inde_ifte : forall R b c d,
  inde (modified_cmd_var (ifte b thendo c elsedo d)) R ->
  inde (modified_cmd_var c) R /\ inde (modified_cmd_var d) R.
intros.
split.
red.
intros.
red in H.
generalize (H s h x v); intro.
apply H1.
simpl.
apply in_or_app.
auto.
red.
intros.
red in H.
generalize (H s h x v); intro.
apply H1.
simpl.
apply in_or_app.
auto.
Qed.

Lemma frame_rule : forall P c Q,
  {{P}} c {{Q}} -> 
  forall R , 
    (inde (modified_cmd_var c) R -> 
      {{ P ** R }} c {{ Q ** R }}).
do 4 intro.
induction H.
(* skip *)
intros.
apply semax_skip.
(* x <- e *)
intros.
apply semax_strengthen_pre with (update_store2 x e (P**R)).
red; intros.
red in H0.
inversion_clear H0 as [h1].
inversion_clear H1 as [h2].
decompose [and] H0; clear H0.
red.
exists h1; exists h2.
split; auto.
split; auto.
split; auto.
red in H.
apply inde_update_store.
simpl in H.
auto.
auto.
apply semax_assign.
(* x <-* e *)
intros.
apply semax_strengthen_pre with (lookup2 x e (P**R)).
red; intros.
red in H0.
red.
inversion_clear H0 as [h1].
inversion_clear H1 as [h2].
decompose [and] H0; clear H0.
unfold lookup2 in H2.
inversion_clear H2 as [p].
inversion_clear H0.
inversion_clear H4 as [z].
inversion_clear H0.
exists p; split; auto; exists z; split.
rewrite H3.
apply heap.lookup_union; auto.
exists h1; exists h2.
split; auto.
split; auto.
split; auto.
apply inde_update_store.
auto.
auto.
apply semax_lookup.
(* e *<- e' *)
intros.
apply semax_strengthen_pre with (update_heap2 e e' (P**R)).
red; intros.
red.
red in H0.
inversion_clear H0 as [h1].
inversion_clear H1 as [h2].
decompose [and] H0; clear H0.
red in H2.
inversion_clear H2 as [p].
inversion_clear H0.
inversion_clear H4 as [z].
inversion_clear H0.
exists p; split; auto.
exists z; split.
rewrite H3.
apply heap.lookup_union; auto.
exists (heap.update p (eval e' s) h1); exists h2.
split.
apply heap.disjoint_update.
auto.
split.
rewrite H3.
eapply heap.equal_update_L.
auto.
apply H4.
auto.
apply semax_mutation.
(* x <-malloc e *)
intros.
apply semax_strengthen_pre with (fun s h =>
  forall n , (((nat_e n) |-> e) -* update_store2 x (nat_e n) (P ** R)) s h).
red; intros.
red; intros.
red in H0.
inversion_clear H0 as [h1].
inversion_clear H3 as [h2].
decompose [and] H0; clear H0.
generalize (H4 n); clear H4; intro.
red in H0.
generalize (H0 h'); clear H0; intro.
assert (h1 # h').
apply heap.equal_union_disjoint with h2.
rewrite <-H5.
intuition.
generalize (H0 (conj H4 (proj2 H1))); clear H0; intro.
generalize (H0 (h1 +++ h')); clear H0; intro.
intuition.
generalize H1; clear H1; intro H0.
red in H0.
red.
exists (h1+++h'); exists h2.
split.
apply heap.disjoint_com.
apply heap.disjoint_union.
split.
apply heap.disjoint_com; auto.
apply heap.equal_union_disjoint with h1.
assert ((h1 +++ h2) = (h2 +++ h1)).
apply heap.union_com.
auto.
rewrite <-H1.
rewrite <-H5.
auto.
split.
Equal_heap.
split; auto.
red in H.
generalize (H s h2 x (loc2val n)); clear H; intro.
simpl in H.
intuition.
apply semax_malloc.
(* free *)
intros.
apply semax_strengthen_pre with (fun s h =>
      exists l,
        val2loc (eval e s) = l /\
        (exists v0, heap.lookup l h = Some v0 /\ (P ** R) s (h --- l))).
red; intros.
inversion_clear H0.
inversion_clear H1.
decompose [and] H0; clear H0.
inversion_clear H2.
decompose [and] H0; clear H0.
inversion_clear H4.
inversion_clear H0.
exists x1.
split; auto.
exists x2.
split.
rewrite H3.
apply heap.lookup_union.
auto.
auto.
exists (x --- x1).
exists x0. 
assert (x0 = x0 --- x1).
apply sym_eq.
apply heap.dif_disjoint with x2.
generalize (heap.lookup_exists_partition x x1 x2 H4); intros.
inversion_clear H0.
inversion_clear H7.
Disjoint_heap.
split.
rewrite H0.
apply heap.dif_disjoint'.
auto.
split; auto.
rewrite H3.
apply trans_eq with ((x +++ x0) --- x1).
auto.
apply trans_eq with ((x --- x1) +++ (x0 --- x1)).
apply heap.dif_union.
apply trans_eq with (heap.dif x0 x1 +++ heap.dif x x1).
apply heap.union_com.
apply heap.dif_disjoint'.
auto.
apply trans_eq with ( x0 +++ heap.dif x x1).
rewrite <- H0.
auto.
apply heap.union_com.
apply heap.disjoint_com.
rewrite H0.
apply heap.dif_disjoint'.
auto.
apply semax_free.
(* sequence *)
intros.
apply semax_seq with (Q ** R0).
apply semax_strengthen_pre with (P ** R0).
red; auto.
generalize (IHsemax1 R0); intro.
apply IHsemax1.
exact (proj1 (inde_seq _ _ _ H1)).
apply (IHsemax2 R0).
apply (proj2 (inde_seq _ _ _ H1)).
(* while true *)
intros.
apply semax_weaken_post with (fun s h =>
  (P ** R) s h /\ eval_b b s = false).
red; intros.
red.
inversion_clear H1.
red in H2.
inversion_clear H2 as [h1].
inversion_clear H1 as [h2].
decompose [and] H2; clear H2.
exists h1; exists h2; auto.
apply semax_strengthen_pre with (fun s h => 
  (P ** R) s h).
red; intros.
auto.
apply semax_while with (P:=P**R).
assert (inde (modified_cmd_var c) R).
auto.
generalize (IHsemax _ H1); intro.
apply semax_strengthen_pre with (fun s h => 
  ((fun s0 h0 => P s0 h0 /\ eval_b b s0 = true) ** R) s h).
red; intros.
red.
inversion_clear H3.
red in H4.
inversion_clear H4 as [h1].
inversion_clear H3 as [h2].
decompose [and] H4; clear H4.
exists h1; exists h2; auto.
auto.
(* semax_conseq *)
intros.
generalize (IHsemax _ H2); intros.
apply semax_strengthen_pre with (P' ** R).
red; intros.
red in H4.
inversion_clear H4 as [h1].
inversion_clear H5 as [h2].
decompose [and] H4; clear H4.
exists h1; exists h2; auto.
apply semax_weaken_post with (Q' ** R).
red; intros.
inversion_clear H4 as [h1].
inversion_clear H5 as [h2].
decompose [and] H4; clear H4.
exists h1; exists h2; auto.
auto.
(* semax_ifte *)
intros.
apply semax_ifte.
assert (inde (modified_cmd_var c) R).
exact (proj1 (inde_ifte _ _ _ _ H1)).
generalize (IHsemax1 _ H2); intro.
apply semax_strengthen_pre with (fun s h => 
  ((fun s0 h0 => P s0 h0 /\ eval_b b s0 = true) ** R) s h 
); auto.
red; intros.
inversion_clear H4.
red in H5.
inversion_clear H5 as [h1].
inversion_clear H4 as [h2].
decompose [and] H5; clear H5.
red.
exists h1; exists h2; auto.
assert (inde (modified_cmd_var d) R).
exact (proj2 (inde_ifte _ _ _ _ H1)).
generalize (IHsemax2 _ H2); intro.
apply semax_strengthen_pre with (fun s h => 
  ((fun s0 h0 => P s0 h0 /\ eval_b b s0 = false) ** R) s h
); auto.
red; intros.
inversion_clear H4.
red in H5.
inversion_clear H5 as [h1].
inversion_clear H4 as [h2].
decompose [and] H5; clear H5.
red.
exists h1; exists h2; auto.
Qed.

Lemma semax_free_global_backwards : forall e v P, 
  {{ (e |-> v) ** P }} free e {{ sep.emp ** P }}.
intros.
apply frame_rule.
apply semax_strengthen_pre with (fun s h => 
  exists l,
    val2loc (eval e s) = l /\
    (exists v0,
      heap.lookup l h = Some v0 /\ sep.emp s (h --- l))).
red; intros.
inversion_clear H.
inversion_clear H0.
exists x.
split; auto.
exists (eval v s).
split.
rewrite H1.
apply heap.lookup_singleton.
red.
eapply trans_eq with ((heap.singleton x (eval v s)) --- x).
rewrite H1; auto.
apply heap.dif_singleton_emp.
apply semax_free.
simpl.
red.
intros.
simpl in H.
tauto.
Qed.

(*
 * more Reynolds' axioms
 *)

Lemma semax_mutation_global : forall P e e',
  {{(fun s' h' => exists e'', ((e |-> e'') s' h'))**P}} e *<- e' {{(e |-> e')**P}}.
intros.
apply frame_rule.
apply semax_strengthen_pre with (update_heap2 e e' (e |-> e')).
red; intros.
inversion_clear H.
red in H0.
inversion_clear H0.
red.
exists x0; split; intuition.
exists (eval x s); split; auto.
rewrite H1.
apply heap.lookup_singleton.
red.
exists x0; split; auto.
apply trans_eq with (heap.update x0 (eval e' s) (heap.singleton x0 (eval x s))).
rewrite H1.
auto.
apply heap.update_singleton.
apply semax_mutation.
simpl.
red; intros.
simpl in H; contradiction.
Qed.

Lemma semax_mutation_global_alternative : forall P e e' e'',
  {{ (e |-> e'') ** P }} e *<- e' {{ (e |-> e') ** P }}.
intros.
apply semax_strengthen_pre with ((fun s' h' => exists e'', (e|->e'') s' h')**P).
red; intros.
red in H.
inversion_clear H.
inversion_clear H0.
decompose [and] H; clear H.
exists x; exists x0.
split; auto.
split; auto.
split; auto.
exists e''.
auto.
apply semax_mutation_global.
Qed.

Lemma semax_mutation_backwards : forall P e e',
  {{fun s h => exists e'', (e|->e''**(e|->e'-*P)) s h}} e *<- e' {{P}}.
intros.
generalize (semax_mutation_global ((e |-> e') -* P) e e'); intro.
apply semax_weaken_post with ((e |-> e') ** ((e |-> e') -* P)).
apply sep.mp.
apply semax_strengthen_pre with
((fun s' h' => exists e'', (e |-> e'') s' h' ) ** ((e |-> e') -* P)).
red; intros.
inversion_clear H0.
red.
inversion_clear H1.
exists x0.
inversion_clear H0.
exists x1.
decompose [and] H1; clear H1.
split; auto.
split; auto.
split; auto.
exists x; auto.
auto.
Qed.

Lemma semax_mutation_backwards_alternative : forall P e e' e'',
  {{ (e |-> e'') ** ((e |-> e') -* P) }} e *<- e' {{ P }}.
intros.
generalize (semax_mutation_global_alternative ((e |-> e') -* P) e e' e''); intro.
apply semax_weaken_post with ((e |-> e') ** ((e |-> e') -* P)).
apply sep.mp.
auto.
Qed.


