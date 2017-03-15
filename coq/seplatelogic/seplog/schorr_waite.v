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
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *)

Load seplog_header.

Notation " s '|b=' b " := (eval_b b s = true) (right associativity, at level 80).
Notation " s '|b!=' b " := (eval_b b s = false) (right associativity, at level 80).


Ltac Step  R :=
  match goal with
    | id: {{?P'}} ?c {{?Q'}} |- {{?P}} ?c {{?Q}} => eapply apply_triple; [apply id | idtac | idtac]
    | id: {{?P'}} ?c {{?Q'}} |- {{?P}} ?c; ?c' {{?Q}} => eapply apply_triple'; [apply id | idtac | idtac]
    | |- {{?P}} ?x <- ?e {{?Q}} => eapply semax_assign'; red
    | |- {{?P}} ?x <- ?e ; ?c {{?Q}} => eapply semax_assign'' with R; [red; intros | idtac]
    | |- {{?P}} ?x <-* ?e {{?Q}} => eapply semax_lookup_backwards'
    | |- {{?P}} ?x <-* ?e ; ?c {{?Q}} =>  eapply semax_lookup_backwards'' with R; [red; intros | idtac]
    | |- {{?P}} ?e1 *<- ?e2 {{?Q}} => eapply semax_mutation_backwards'
    | |- {{?P}} ?e1 *<- ?e2 ; ?c {{?Q}} => eapply semax_mutation_backwards'' with R; [red; intros | idtac]
    | |- {{?P}} while ?b ?c1 {{?Q}} => eapply semax_while' with R
    | |- {{?P}} while ?b ?c1 ; ?c2 {{?Q}} => eapply semax_while'' with R; [red; intros | idtac | idtac]
    | |- {{?P}} skip {{?Q}} =>  eapply semax_skip'
    | |- {{?P}} ifte ?b thendo ?c1 elsedo ?c2 {{?Q}} =>  eapply semax_ifte
    | |- {{?P}} (ifte ?b thendo ?c1 elsedo ?c2); ?c' {{?Q}} => apply semax_seq with R; [eapply semax_ifte; [idtac| idtac] | idtac]
    | |- {{?P}} ?c1; ?c2 {{?Q}} => apply semax_seq with R; [idtac| idtac]
  end.


Ltac Decompose_hyp := 
  match goal with
    | id: ?P1 /\ ?P2 |- _ => (decompose [and] id; clear id); Decompose_hyp
    | id: (?P1 ** ?P2) ?s ?h |- _ =>
       (let x:=fresh in (
           inversion_clear id as [x X];
           let y:= fresh in (
              inversion_clear X as [y Y];
              decompose [and] Y; clear Y
           )
        )); Decompose_hyp
    | id: ex ?P |- _ => (inversion_clear id); Decompose_hyp
    | _ => idtac
  end.

(******************)
(*   rewriting    *)
(******************)

Lemma expr_store_update_rewrite: forall e x p s,
  eval (expr_rewrite e (var_e x) (int_e p)) s = eval e (store.update  x p s).
induction e; simpl; intros; auto.

generalize (beq_nat_classic v x); intro X; inversion_clear X.
rewrite H.
generalize (beq_nat_true _ _ H); intro; subst v.
rewrite store.lookup_update'.
auto.
rewrite H.
generalize (beq_nat_false _ _ H); intro.
rewrite <- (store.lookup_update); auto.
rewrite IHe1; rewrite IHe2; auto.
rewrite IHe1; rewrite IHe2; auto.
rewrite IHe1; rewrite IHe2; auto.
rewrite IHe1; rewrite IHe2; auto.
Qed.

Lemma expr_b_store_update_rewrite: forall b x p s,
  eval_b (expr_b_rewrite b (var_e x) (int_e p)) s = eval_b b (store.update  x p s).
induction b; simpl; intros; auto.
repeat rewrite expr_store_update_rewrite; auto.
repeat rewrite expr_store_update_rewrite; auto.
repeat rewrite expr_store_update_rewrite; auto.
repeat rewrite expr_store_update_rewrite; auto.
rewrite IHb; auto.
rewrite IHb1; rewrite IHb2; auto.
rewrite IHb1; rewrite IHb2; auto.
Qed.

Lemma mapsto_store_update_rewrite: forall e1 e2 x p s h,
  ((expr_rewrite e1 (var_e x) (int_e p)) |-> (expr_rewrite e2 (var_e x) (int_e p))) s h ->
  (e1 |-> e2) (store.update x p s) h.
intros.
red in H; red.
inversion_clear H.
inversion_clear H0.
exists x0.
split.
rewrite <- expr_store_update_rewrite.
auto.
rewrite <- expr_store_update_rewrite.
auto.
Qed.

(* the fields of the node structure *)

Definition l := 0%Z.
Definition r := 1%Z.
Definition c := 2%Z.
Definition m := 3%Z.
Hint Unfold l.
Hint Unfold r.
Hint Unfold c.
Hint Unfold m.

(* a tactic unfolding fields name to their offset *)
Ltac Unfolds_fields :=
  unfold l; unfold r; unfold c; unfold m.

(* the Schorr-Waite algorithm *)

Definition SW (t p q:var.v) (root: nat):=
   (t <- (nat_e root));
   (p <- (nat_e 0));
   (q <-* (t -.> m));
   while (((var_e p) =/= (nat_e 0)) ||| (((var_e t) =/= (nat_e 0)) &&& ((var_e q) =/= (nat_e 1)))) (
       (ifte (((var_e t) == (nat_e 0)) ||| ((var_e q) == (nat_e 1))) thendo
           (
             (q <-* (p -.> c));
             ifte ((var_e q) == (nat_e 1)) thendo (
                (* pop *)
                (q <- (var_e t)); (t <- (var_e p)); (p <-* (p -.> r)); ((t -.>r) *<- (var_e q)) 
             ) elsedo (
                (* swing *)
                (q <- (var_e t)); (t <-* (p -.> r)); ((p -.> r) *<- (p -.> l)); ((p -.> l) *<- (var_e q)); ((p -.> c) *<- (nat_e 1))
             )
           ) elsedo (
                (* push *)
                (q <- (var_e p)); (p <- (var_e t)); (t <-* (t -.> l)); ((p -.> l) *<- (var_e q)); ((p -.> m) *<- (nat_e 1)); ((p -.> c) *<- (nat_e 0))
           )
       ); (q <-* (t -.> m))
   ).


(* graph definition in separation logic
     Graph (N,E): store -> heap -> Prop.  where N is the list of graph node(adresse) and E the list of edge 
     (triple: node1, node2, node3. meaning there is an edge from node1 to node 2 and a node from node1 to node3)
*)

Inductive Graph: list (nat * nat * nat) -> list (nat * nat * nat) -> store.s -> heap.h -> Prop := 

empty_N: forall s h, sep.emp s h -> Graph nil nil s h

| empty_E: forall n l s h1 h2 h c m, 
       n <> 0 ->
       h1 # h2 ->
       h = h1 +++ h2 ->
       ((nat_e n) |--> ((nat_e 0)::(nat_e 0)::(nat_e c)::(nat_e m)::nil)) s h1 ->
       Graph l nil s h2 ->
       Graph ((n,c,m)::l) nil s h

| elim_E: forall ln n1 n2 n3 le s h h1 h2 c m, 
       (n2 = 0 \/ In (n2,c,m) ln) ->
       (n3 = 0 \/ In (n3,c,m) ln) ->
       h1 # h2 ->
       h = h1 +++ h2 ->
       ((nat_e n1)|-->((nat_e n2)::(nat_e n3)::(nat_e c)::(nat_e m)::nil)) s h1 ->
       (((nat_e n1)|-->((nat_e 0)::(nat_e 0)::(nat_e c)::(nat_e m)::nil)) -* (Graph ln (le))) s h2 ->
       Graph ln ((n1, n2, n3)::le) s h.

Lemma Graph_inde_store: forall N E s s' h,
 Graph N E s h -> Graph N E s' h.
intros.
induction H.
eapply empty_N.
intuition.
eapply empty_E.
apply H.
apply H0.
auto.
intuition.
intuition.
eapply elim_E; auto.
apply H.
apply H0.
apply H1.
auto.
intuition.
Intro_sepimp h1' h'.
apply H5 with (h' := h1').
split; auto.
intuition.
Qed.

Lemma Graph_less_edge: forall N E s h,
  Graph N E s h -> exists h', Graph N nil s h'.
intros.
induction H.
exists heap.emp.
eapply empty_N.
red; auto.
exists (h1 +++ h2).
eapply empty_E.
apply H.
apply H0.
auto.
intuition.
intuition.





Lemma Graph_node_unique_store: forall N E s h n m c,
  Graph N E s h ->
  
  
 


(* this specification is incomplete: only assert that the shape of the graph does not change *)
(* Precondiction of Schorr-Waite *)

Definition SW_precond (N: list nat) (E: list (nat * nat * nat)) (root: nat): assert := 
  fun s h => Graph N E s h /\  In root N.

(* Postcondiction of Schorr-Waite *)

Definition SW_postcond (N: list nat) (E: list (nat * nat * nat)) : assert := 
  Graph N E.

(* Specification of Schorr-Waite *)

Definition t := 0.
Definition p := 1.
Definition q := 2.
Hint Unfold t.
Hint Unfold p.
Hint Unfold q.

Definition SW_specif : Prop := 
   forall root N E,
          {{SW_precond N E root}}
             SW t p q root
          {{SW_postcond N E}}.
 
(* verification of Schorr-Waite specification *)
Lemma SW_verif : SW_specif.
unfold SW_specif.
intros.
unfold SW.
unfold SW_precond.
unfold SW_postcond.

Step (
fun s h => 
  Graph N E s h /\
  In root N /\
  (s |b= (var_e t) == (nat_e root))
).

Decompose_hyp.
red; split.
eapply Graph_inde_store; apply H0.
split; auto.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.

Step (
fun s h => 
  Graph N E s h /\
  In root N /\
  (s |b= (var_e t) == (nat_e root)) /\
  (s |b= (var_e p) == (nat_e 0))
).

Decompose_hyp.
red; split.
eapply Graph_inde_store; apply H0.
split; auto.
split; rewrite <- expr_b_store_update_rewrite; Omega_exprb.



Admitted.



(* old version *)

(*
(* the tree structure *)
Inductive tree: Set :=
     leaf: tree
     | node: nat -> nat -> tree -> tree -> tree.


(* the assertion repreesents a well formed Schorr-Waite tree by a tree starting at a cell*)
Inductive SW_tree: tree -> nat -> store.s -> heap.h -> Prop :=
    SW_leaf: forall adr s h,
                       Emp s h ->
                       adr = 0 ->
                       SW_tree (leaf) adr s h
    | SW_node: forall t1 t2 l r c m adr s h h1 h2,
			h1 # h2 ->
	                h === h1 +++ h2 ->
                        ((nat_e adr) |--> ((nat_e l)::(nat_e r)::(nat_e c)::(nat_e m)::nil)) s h1 ->
			((SW_tree t1 l) ** (SW_tree t2 r)) s h2 ->
                        SW_tree (node c m t1 t2) adr s h.

(* this assertion represents a well formed Schorr-Waite tree by a tree starting at a cell where all node are marked*)
Inductive SW_marked_tree: tree -> nat -> store.s -> heap.h -> Prop :=
    SW_marked_leaf: forall adr s h,
                       SW_tree (leaf) adr s h -> 
                       SW_marked_tree (leaf) adr s h
    | SW_marked_node: forall t1 t2 l r c m adr s h h1 h2,
			h1 # h2 ->
	                h === h1 +++ h2 ->
                        ((nat_e adr) |--> ((nat_e l)::(nat_e r)::(nat_e 1)::(nat_e 1)::nil)) s h1 ->
                        ((SW_marked_tree t1 l) ** (SW_marked_tree t2 r)) s h2 ->
                        SW_marked_tree (node c m t1 t2) adr s h.

(* Precondiction of Schorr-Waite *)

Definition SW_precond (t:tree) (root:nat) : assert := SW_tree t root.

(* Postcondiction of Schorr-Waite *)

Definition SW_postcond (t:tree) (root:nat) : assert := SW_marked_tree t root.

(* Specification of Schorr-Waite *)

Definition SW_specif : Prop := 
   forall sp root t p q,
      var.set (t::p::q::nil) ->
          {{SW_precond sp root}}
             SW t p q root
          {{SW_postcond sp root}}.



(* yapuka *)
Admitted.
*)
