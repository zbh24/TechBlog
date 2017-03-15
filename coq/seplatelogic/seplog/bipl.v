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

Require Import List.
Require Import ZArith.
Require Import List.
Require Import EqNat.
Require Import Classical.
Require Import Bool.

Require Import util.
Require Import heap.

Module Type VAR.
  Parameter v : Set.
  Parameter eqdec : forall (x y : v), {x=y} + {x <> y}.
  Parameter fresh : v -> list v -> Prop.
  Parameter set : list v -> Prop.
End VAR.

Module var <: VAR with Definition v := nat.
  Definition v := nat.
  Definition eqdec := eq_nat_dec.
  Fixpoint fresh (x:v) (he:list v) {struct he} : Prop :=
    match he with
      | nil => True
      | hd::tl => x <> hd /\ fresh x tl
    end.
  
  Fixpoint set (he:list v) : Prop :=
    match he with
      nil => True
      | hd::tl => fresh hd tl /\ set tl
    end.
End var.

(* this tactic proves that two variables are different using a (var.set (...::nil)) hypothesis *)
Ltac Var_uneq :=
   match goal with 
      | id: ?v <> ?v' |- ?v <> ?v' => auto
      | id: ?v' <> ?v |- ?v <> ?v' => auto
      | id: var.fresh ?v ?l |- ?v <> ?v' =>  let x := fresh in
                    (inversion_clear id as [x X]; decompose [and] X; clear X); Var_uneq
      | id: var.fresh ?v' ?l |- ?v <> ?v' => let x := fresh in
                    (inversion_clear id as [x X]; decompose [and] X; clear X); Var_uneq
      | id: var.set ?l |- ?v <> ?v' => 
             let x := fresh in
                    (inversion_clear id as [x X]; decompose [and] X; clear X); Var_uneq
      | _ => fail
   end.

(******************************************************************************)

(* Store *)

Module Type STORE.
  Parameter s : Set.
  Parameter emp : s.
  Parameter lookup : var.v -> s -> val.
  Parameter update : var.v -> val -> s -> s.
  Parameter lookup_emp : forall x,
    lookup x emp = 0%Z.
  Parameter lookup_update : forall x y z st,
    x <> y -> lookup x st = lookup x (update y z st).
  Parameter lookup_update' : forall x z st,
    lookup x (update x z st) = z.
  Parameter extensionality: forall st1 st2, (forall x, lookup x st1 = lookup x st2) -> st1 = st2.
  Parameter update_update: forall s x x' v v',
	x <> x' ->
	update x v (update x' v' s) = update x' v' (update x v s).
  Parameter update_update': forall s x v v',
	update x v (update x v' s) = update x v s.
  Parameter update_lookup : forall s x, 
    update x (lookup x s) s = s.
  Parameter update_lookup_update: forall x v s, 
    update x (lookup x s) (update x v s) = s.
End STORE.

Module non_null_integer.
  Inductive negpos : Set :=
    neg : positive -> negpos
    | pos : positive -> negpos.
  Definition elem := negpos.
End non_null_integer.

Module store_heap := map Loc non_null_integer.

Module store : STORE.
  Definition s := store_heap.h.

  Definition emp : s := store_heap.emp.
  
  Import non_null_integer.

  

  (* Extract the value of a var from a store, default value is Z0 *)
  Definition lookup (w:var.v) (st:s) : Z := 
    match store_heap.lookup w st with
      Some (pos x) => Zpos x
      | Some (neg x) => Zneg x
      | None => Z0
    end.

  (* update of the value of a variable in a store *)
  Definition update (i:var.v) (w:Z) (st:s) : s :=
    match w with
      Z0 => store_heap.dif st i
      | Zneg p => store_heap.union (store_heap.singleton i (neg p)) st
      | Zpos p => store_heap.union (store_heap.singleton i (pos p)) st
    end.

  Lemma lookup_emp : forall x,
    lookup x emp = 0%Z.
    unfold lookup; unfold emp; intros; rewrite store_heap.lookup_emp; auto.
  Qed.

  Lemma lookup_update : forall x y z st,
    x <> y -> lookup x st = lookup x (update y z st).
    intros.
    unfold lookup.
    unfold update.
    destruct z.
    rewrite store_heap.lookup_dif'.
    auto.
    auto.
    elim store_heap.lookup_update.
    auto.
    auto.
    elim store_heap.lookup_update.
    auto.
    auto.
  Qed.

  Lemma lookup_update' : forall w z st,
    lookup w (update w z st) = z.
    intros.
    unfold lookup.
    unfold update.
    destruct z.
    rewrite store_heap.lookup_dif.
    auto.
    rewrite store_heap.lookup_update'.
    auto.
    rewrite store_heap.lookup_update'.
    auto.
  Qed.

  Lemma extensionality: forall st1 st2, 
    (forall x, lookup x st1= lookup x st2) -> st1 = st2.
    intros.
    apply store_heap.extensionality.
    unfold lookup in H.
    intro.
    generalize (H x); intros.
    destruct (store_heap.lookup x st1).
    destruct v.
    destruct (store_heap.lookup x st2).
    destruct v.
    injection H0; intro; subst p0; auto.
    discriminate H0.
    discriminate H0.
    destruct (store_heap.lookup x st2).
    destruct v.
    discriminate H0.
    injection H0; intro; subst p0; auto.
    discriminate H0.
    destruct (store_heap.lookup x st2).
    destruct v.
    discriminate H0.
    discriminate H0.
    auto.
  Qed.

  Lemma update_update: forall s x x' v v', x <> x' ->
    update x v (update x' v' s) = update x' v' (update x v s).
    intros.
    eapply extensionality.
    intros.
    generalize (beq_nat_classic x0 x); intro X; inversion_clear X.
    generalize (beq_nat_true x0 x H0); intros; subst x0.
    clear H0.
    rewrite lookup_update'.
    rewrite <- lookup_update.
    rewrite lookup_update'.
    auto.
    auto.
    generalize (beq_nat_false x0 x H0); intros; clear H0.
    rewrite <- lookup_update; [idtac | auto].
    generalize (beq_nat_classic x0 x'); intro X; inversion_clear X.
    generalize (beq_nat_true x0 x' H0); intros; subst x0; clear H0.
    rewrite lookup_update'.
    rewrite lookup_update'.
    auto.
    generalize (beq_nat_false x0 x' H0); intros; clear H0.
    rewrite <- lookup_update; [idtac | auto].
    rewrite <- lookup_update; [idtac | auto].
    rewrite <- lookup_update; [idtac | auto].   
    auto.
  Qed.   
  
  Lemma update_update': forall s x v v',
    update x v (update x v' s) = update x v s.
    intros.
    eapply extensionality.
    intros.
    generalize (beq_nat_classic x0 x); intro X; inversion_clear X.
    generalize (beq_nat_true x0 x H); intros; subst x0; clear H.
    rewrite lookup_update'.
    rewrite lookup_update'.
    auto.
    generalize (beq_nat_false x0 x H); intros; clear H.
    rewrite <- lookup_update; [idtac | auto].
    rewrite <- lookup_update; [idtac | auto].
    rewrite <- lookup_update; [idtac | auto].
    auto.
  Qed.
  
  Lemma update_lookup : forall s x, 
    update x (lookup x s) s = s.
    intros.
    apply extensionality.
    intros.
    generalize (beq_nat_classic x0 x); intro X; inversion_clear X.
    assert (x0=x).
    apply beq_nat_true; auto.
    subst x0; clear H.
    rewrite lookup_update'.
    auto.
    elim lookup_update.
    auto.
    apply beq_nat_false; auto.
  Qed.
    
  Lemma update_lookup_update: forall x v s, 
    update x (lookup x s) (update x v s) = s.
    intros.
    apply extensionality.
    intros.
    generalize (beq_nat_classic x0 x); intro X; inversion_clear X.
    assert (x0=x).
    apply beq_nat_true; auto.
    subst x0; clear H.
    rewrite lookup_update'.
    auto.
    elim lookup_update.
    elim lookup_update.
    auto.
    apply beq_nat_false; auto.
    apply beq_nat_false; auto.
  Qed.

End store.

(******************************************************************************)

(* Expressions definition *)

Inductive expr : Set :=
  var_e : var.v -> expr
| int_e : val -> expr
| add_e : expr -> expr -> expr
| min_e : expr -> expr -> expr
| mul_e : expr -> expr -> expr
| div_e : expr -> expr -> expr
| mod_e : expr -> expr -> expr.

Definition nat_e x := int_e (Z_of_nat x).

Definition null := int_e 0%Z.

Notation "e1 '+e' e2" := (add_e e1 e2) (at level 79) : sep_scope.
Notation "e1 '-e' e2" := (min_e e1 e2) (at level 79) : sep_scope.
Notation "e1 '*e' e2" := (mul_e e1 e2) (at level 79) : sep_scope.
Notation "e1 '/e' e2" := (div_e e1 e2) (at level 79) : sep_scope.
Notation "e1 'mode' e2" := (mod_e e1 e2) (at level 79) : sep_scope.

Open Local Scope sep_scope.

Fixpoint expr_var (e:expr) {struct e} : list var.v :=
  match e with
    var_e x => x::nil
    | int_e z => nil
    | add_e e1 e2 => expr_var e1 ++ expr_var e2
    | min_e e1 e2 => expr_var e1 ++ expr_var e2
    | mul_e e1 e2 => expr_var e1 ++ expr_var e2
    | div_e e1 e2 => expr_var e1 ++ expr_var e2
    | mod_e e1 e2 => expr_var e1 ++ expr_var e2
  end.

Fixpoint expr_eq (e1:expr) (e2:expr) {struct e1} : bool :=
  match e1 with
    var_e w1 => match e2 with
                  var_e w2 => beq_nat w1 w2
                  | _ => false
                end
    | int_e i1 => match e2 with
                    int_e i2 => Zeq_bool i1 i2
                    | _ => false
                  end
    | add_e e11 e12 => match e2 with
                         add_e e21 e22 =>  andb (expr_eq e11 e21) (expr_eq e12 e22)
                         | _ => false
                       end
    | min_e e11 e12 => match e2 with
                         min_e e21 e22 => andb (expr_eq e11 e21) (expr_eq e12 e22)
                         | _ => false
                       end
    | mul_e e11 e12 => match e2 with
                         mul_e e21 e22 => andb (expr_eq e11 e21) (expr_eq e12 e22)
                         | _ => false
                       end
    | div_e e11 e12 => match e2 with
                         div_e e21 e22 => andb (expr_eq e11 e21) (expr_eq e12 e22)
                         | _ => false
                       end
    | mod_e e11 e12 => match e2 with
                         mod_e e21 e22 => andb (expr_eq e11 e21) (expr_eq e12 e22)
                         | _ => false
                       end
  end.

Fixpoint expr_rewrite (e:expr) (patern:expr) (rep:expr) {struct e} : expr :=
  match e with
    var_e w => match expr_eq e patern with
                 true => rep
                 | false => e
               end
    | int_e i => match expr_eq e patern with
                   true => rep
                   | false => e
                 end
    | add_e e1 e2 => match expr_eq e patern with
                       true => rep
                       | false => add_e (expr_rewrite e1 patern rep) (expr_rewrite e2 patern rep)
                     end
    | min_e e1 e2 => match expr_eq e patern with
                       true => rep
                       | false => min_e (expr_rewrite e1 patern rep) (expr_rewrite e2 patern rep)
                     end
    | mul_e e1 e2 => match expr_eq e patern with
                       true => rep
                       | false => mul_e (expr_rewrite e1 patern rep) (expr_rewrite e2 patern rep)
                     end
    | div_e e1 e2 => match expr_eq e patern with
                       true => rep
                       | false => div_e (expr_rewrite e1 patern rep) (expr_rewrite e2 patern rep)
                     end
    | mod_e e1 e2 => match expr_eq e patern with
                       true => rep
                       | false => mod_e (expr_rewrite e1 patern rep) (expr_rewrite e2 patern rep)
                     end
end.
(*
Lemma store_lookup_update' : forall x z st,
    store.lookup x (store.update x z st) = z.
  intros.
  rewrite store.lookup_update'.
  auto.
Qed.

Lemma store_lookup_update : forall x y z st,
    x <> y -> store.lookup x (store.update y z st) = store.lookup x st.
  intros.
  elim store.lookup_update; [auto | auto].
Qed.
*)
(* Compute the value of an expression on a store *)
Fixpoint eval (e:expr) (s:store.s) {struct e} : Z :=
match e with
  var_e w => store.lookup w s
  | int_e i => i
  | add_e e1 e2 => Zplus (eval e1 s) (eval e2 s)
  | min_e e1 e2 => Zminus (eval e1 s) (eval e2 s)
  | mul_e e1 e2 => Zmult (eval e1 s) (eval e2 s)
  | div_e e1 e2 => Zdiv (eval e1 s) (eval e2 s)
  | mod_e e1 e2 => Zmod (eval e1 s) (eval e2 s)
end.

Lemma eval_store_update: forall e x v s,
  eval e (store.update x (eval v s) s) = eval (expr_rewrite e (var_e x) v) s.
  induction e.
  simpl; intros.
  generalize (beq_nat_classic v x); intro X; inversion_clear X.
  generalize (beq_nat_true _ _ H); intros.
  subst v.
  rewrite H.
  rewrite store.lookup_update'.
  auto.
  rewrite H.
  generalize (beq_nat_false v x H); intros.
  rewrite <- store.lookup_update.
  auto.
  auto.
  auto.
  simpl; intros.
  rewrite IHe1; rewrite IHe2; auto.
  simpl; intros.
  rewrite IHe1; rewrite IHe2; auto.
  simpl; intros.
  rewrite IHe1; rewrite IHe2; auto.
  simpl; intros.
  rewrite IHe1; rewrite IHe2; auto.
  simpl; intros.
  rewrite IHe1; rewrite IHe2; auto.
Qed.

(* TODO: confusing name *)
Lemma inde_expr : forall e l,
  inter (expr_var e) l nil ->
  forall x, In x l ->
    forall s z,
      eval e s = eval e (store.update x z s).
  induction e.
  simpl.
  intros.
  rewrite <- store.lookup_update.
  auto.
  red in H.
  generalize (H x); intro.
  inversion_clear H1.
  intro.
  subst x.
  apply H2.
  simpl; auto.
  simpl.
  auto.
  intros.
  cut (inter (expr_var e1) l nil /\ inter (expr_var e2) l nil).
  intro.
  simpl.
  inversion_clear H1.
  rewrite (IHe1 _ H2 _ H0 s z).
  rewrite (IHe2 _ H3 _ H0 s z).
  auto.
  simpl in H.
  apply inter_app.
  auto.
  intros.
  cut (inter (expr_var e1) l nil /\ inter (expr_var e2) l nil).
  intro.
  simpl.
  inversion_clear H1.
  rewrite (IHe1 _ H2 _ H0 s z).
  rewrite (IHe2 _ H3 _ H0 s z).
  auto.
  simpl in H.
  apply inter_app.
  auto.
  intros.
  cut (inter (expr_var e1) l nil /\ inter (expr_var e2) l nil).
  intro.
  simpl.
  inversion_clear H1.
  rewrite (IHe1 _ H2 _ H0 s z).
  rewrite (IHe2 _ H3 _ H0 s z).
  auto.
  simpl in H.
  apply inter_app.
  auto.
  intros.
  simpl.
  cut (inter (expr_var e1) l nil /\ inter (expr_var e2) l nil).
  intro.
  inversion_clear H1.
  rewrite (IHe1 _ H2 _ H0 s z).
  rewrite (IHe2 _ H3 _ H0 s z).
  auto.
  simpl in H.
  apply inter_app.
  auto.
  intros.
  simpl.
  cut (inter (expr_var e1) l nil /\ inter (expr_var e2) l nil).
  intro.
  inversion_clear H1.
  rewrite (IHe1 _ H2 _ H0 s z).
  rewrite (IHe2 _ H3 _ H0 s z).
  auto.
  simpl in H.
  apply inter_app.
  auto.
Qed.

Lemma expr_inde_var: forall e s v x,
  ~In x (expr_var e) ->
  eval e s = eval e (store.update x v s).
  induction e; simpl; intros; auto.
  rewrite <- store.lookup_update; auto.
  rewrite <- IHe1; intuition.
  rewrite <- IHe2; intuition.
  rewrite <- IHe1; intuition.
  rewrite <- IHe2; intuition.
  rewrite <- IHe1; intuition.
  rewrite <- IHe2; intuition.
  rewrite <- IHe1; intuition.
  rewrite <- IHe2; intuition.
  rewrite <- IHe1; intuition.
  rewrite <- IHe2; intuition.
Qed.

(* notation for structures *)
Definition field x f := var_e x +e int_e f.
Notation "x '-.>' f " := (field x f) (at level 79) : sep_scope.

(* boolean expression *)
(* TODO: add lt_b, le_b *)
Inductive expr_b : Set :=
  true_b: expr_b
| eq_b : expr -> expr -> expr_b
| neq_b : expr -> expr -> expr_b
| ge_b : expr -> expr -> expr_b
| gt_b : expr -> expr -> expr_b
| neg_b : expr_b -> expr_b
| and_b : expr_b -> expr_b -> expr_b
| or_b : expr_b -> expr_b -> expr_b.

Notation "e == e'" := (eq_b e e') (at level 78) : sep_scope.
Notation "e =/= e'" := (neq_b e e') (at level 78) : sep_scope.
Notation "e &&& e'" := (and_b e e') (at level 78) : sep_scope.
Notation "e ||| e'" := (or_b e e') (at level 78) : sep_scope.
Notation "e >>= e'" := (ge_b e e') (at level 78) : sep_scope.
Notation "e >> e'" := (gt_b e e') (at level 78) : sep_scope.

Fixpoint expr_b_var (e:expr_b) : list var.v :=
  match e with 
    true_b => nil
    | eq_b e1 e2 => expr_var e1 ++ expr_var e2
    | neq_b e1 e2 => expr_var e1 ++ expr_var e2
    | ge_b e1 e2 => expr_var e1 ++ expr_var e2
    | gt_b e1 e2 => expr_var e1 ++ expr_var e2
    | and_b e1 e2 => expr_b_var e1 ++ expr_b_var e2
    | or_b e1 e2 => expr_b_var e1 ++ expr_b_var e2
    | neg_b e => expr_b_var e
  end.

Fixpoint expr_b_eq (e1: expr_b) (e2: expr_b) {struct e1} : bool :=
match e1 with
  true_b => match e2 with
              true_b => true
              | _ => false
            end
  | f == g => match e2 with
                f' == g' => andb (expr_eq f f') (expr_eq g g')
                | _ => false
              end   
  | f =/= g => match e2 with
                 f' =/= g' => andb (expr_eq f f') (expr_eq g g')
                 | _ => false
               end   
  | f >>= g => match e2 with
                 f' >>= g' => andb (expr_eq f f') (expr_eq g g')
                 | _ => false
               end   
  | f >> g => match e2 with
                f' >> g' => andb (expr_eq f f') (expr_eq g g')
                | _ => false
              end   
  | f &&& g => match e2 with
                 f' &&& g' => andb (expr_b_eq f f') (expr_b_eq g g')
                 | _ => false
               end   
  | f ||| g => match e2 with
                 f' ||| g' => andb (expr_b_eq f f') (expr_b_eq g g')
                 | _ => false
               end   
  | neg_b e =>  match e2 with
                  neg_b e' => (expr_b_eq e e')
                  | _ => false
                end   
end.

Fixpoint expr_b_rewrite (e: expr_b) (patern: expr) (rep: expr) {struct e}: expr_b :=
  match e with
    true_b => true_b
    | f == g => expr_rewrite f patern rep == expr_rewrite g patern rep
    | f =/= g => expr_rewrite f patern rep =/= expr_rewrite g patern rep
    | f >>= g => expr_rewrite f patern rep >>= expr_rewrite g patern rep
    | f >> g => expr_rewrite f patern rep >> expr_rewrite g patern rep
    | f &&& g => expr_b_rewrite f patern rep &&& expr_b_rewrite g patern rep
    | f ||| g => expr_b_rewrite f patern rep ||| expr_b_rewrite g patern rep
    | neg_b e => neg_b (expr_b_rewrite e patern rep)
  end.  

(* Compute the value of an boolean expression *)
Fixpoint eval_b (e:expr_b) (s:store.s) {struct e} : bool :=
match e with
  true_b => true
  | f == g => Zeq_bool (eval f s) (eval g s)
  | f =/= g => negb (Zeq_bool (eval f s) (eval g s))
  | f >>= g => Zge_bool (eval f s) (eval g s)
  | f >> g => Zgt_bool (eval f s) (eval g s)
  | f &&& g => andb (eval_b f s) (eval_b g s)
  | f ||| g => orb (eval_b f s) (eval_b g s)
  | neg_b e => negb (eval_b e s)
end.

Lemma eval_b_store_update: forall b x v s,
  eval_b b (store.update x (eval v s) s) = eval_b (expr_b_rewrite b (var_e x) v) s.
  induction b.
  simpl; intros.
  auto.
  simpl; intros; repeat rewrite eval_store_update; auto.
  simpl; intros; repeat rewrite eval_store_update; auto.
  simpl; intros; repeat rewrite eval_store_update; auto.
  simpl; intros; repeat rewrite eval_store_update; auto.
  simpl; intros; rewrite IHb; auto.
  simpl; intros; rewrite IHb1; rewrite IHb2; auto.
  simpl; intros; rewrite IHb1; rewrite IHb2; auto.
Qed.

Fixpoint expr_b_sem (e: expr_b) (s: store.s) {struct e} : Prop :=
match e with
  true_b => True
  | f == g => eval f s = eval g s
  | f =/= g => (eval f s <> eval g s)
  | f >>= g => (eval f s >= eval g s)%Z
  | f >> g => (eval f s > eval g s)%Z
  | f &&& g => expr_b_sem f s /\ expr_b_sem g s
  | f ||| g => expr_b_sem f s \/ expr_b_sem g s
  | neg_b e => ~ expr_b_sem e s
end. 

Lemma expr_b_inde_var: forall b s v x,
   ~In x (expr_b_var b) ->
   eval_b b s = eval_b b (store.update x v s).
  induction b; simpl; intros; auto.
  rewrite <- expr_inde_var; intuition.
  rewrite <- expr_inde_var; intuition.
  rewrite <- expr_inde_var; intuition.
  rewrite <- expr_inde_var; intuition.
  rewrite <- expr_inde_var; intuition.
  rewrite <- expr_inde_var; intuition.
  rewrite <- expr_inde_var; intuition.
  rewrite <- expr_inde_var; intuition.
  rewrite <- IHb; intuition.
  rewrite <- IHb1; intuition.
  rewrite <- IHb2; intuition.
  rewrite <- IHb1; intuition.
  rewrite <- IHb2; intuition.
Qed.

Lemma expr_b_semantic_good : forall e s,
  eval_b e s = true <-> expr_b_sem e s.
  induction e; simpl.

  split; auto.

  split; intros.
  apply Zeq_bool_true; auto.
  rewrite H.
  apply Zeq_bool_refl.

  split; intros.
  apply Zeq_bool_false'.
  apply negb_true_is_false; auto.
  generalize (Zeq_bool_false'' _ _ H); intro.
  rewrite H0.
  reflexivity.

  split; intros.
  apply Zge_bool_true; auto.
  apply Zge_bool_true'; auto.
  
  split; intros.
  apply Zgt_bool_true; auto.
  apply Zgt_bool_true'; auto.

  split; intros.
  generalize (IHe s); intro.
  assert (~ eval_b e s = true).
  intro.
  rewrite H1 in H; discriminate.
  tauto.
  generalize (IHe s); intro.
  destruct (eval_b e s).
  tauto.
  auto.
  
  split; intros.
  generalize (IHe1 s); intro X; inversion_clear X.
  generalize (IHe2 s); intro X; inversion_clear X.
  generalize (andb_prop _ _ H); intro X; inversion_clear X.
  intuition.
  intros.
  apply andb_true_intro.
  generalize (IHe1 s); intro X; inversion_clear X.
  generalize (IHe2 s); intro X; inversion_clear X.
  intuition.
  
  split; intros.
  generalize (IHe1 s); intro X; inversion_clear X.
  generalize (IHe2 s); intro X; inversion_clear X.
  generalize (orb_prop _ _ H); intro.
  intuition.
  intros.
  apply orb_true_intro.
  generalize (IHe1 s); intro X; inversion_clear X.
  generalize (IHe2 s); intro X; inversion_clear X.
  intuition.
Qed.

Lemma expr_b_false_negb_true: forall b s,
    eval_b b s = false -> eval_b (neg_b b) s = true.
  intros; simpl.
  apply negb_false_is_true.
  rewrite negb_elim.
  auto.
Qed.

Lemma expr_b_true_negb_false: forall b s,
    eval_b (neg_b b) s = true -> eval_b b s = false.
  intros; simpl.
  apply negb_true_is_false.
  simpl in H.
  auto.
Qed.

(*
Lemma t1: forall e3 e4 e1 e2 s,
    eval_b ((e3 >> e4) &&& (e1 >>= e2)) s = true -> 
    eval_b (neg_b ((e3 +e e1) >> (e4 +e e2))) s = false.
intros.
Omega_exprb.
Qed.
*)

Open Local Scope heap_scope.

(* assertions *)

Definition assert := store.s -> heap.h -> Prop. 

(* The True/False assertions *)

Definition TT : assert := fun s h => True.

Definition FF : assert := fun s h => False.

Definition And (P Q:assert) : assert := fun s h => P s h /\ Q s h.

Module sep.

(* The separation conjunction *)

Definition con (P Q:assert) : assert := fun s h =>
  exists h1, exists h2, h1 # h2 /\ h = h1 +++ h2 /\ P s h1 /\ Q s h2.

Notation "P ** Q" := (con P Q) (at level 80).

Lemma con_inde_store: forall P Q s s' h,
  ((P ** Q) s h) -> 
  (forall s s' h, P s h -> P s' h) -> 
  (forall s s' h, Q s h -> Q s' h) ->
  ((P ** Q) s' h).
  intros.
  red in H.
  red.
  inversion_clear H.
  inversion_clear H2.
  decompose [and] H; clear H.
  exists x; exists x0.
  intuition.
  eapply H0.
  apply H3.
  eapply H1.
  apply H6.
Qed.

(* The separation implication *)

Definition imp (P Q:assert) : assert := fun s h =>
  forall h', h # h' /\ P s h' ->
    forall h'', h'' = h +++ h' -> Q s h''.

Notation "P -* Q" := (imp P Q) (at level 80).

(** Assertions lemma *)

Definition entails (P Q:assert) : Prop :=
  forall s h, P s h -> Q s h.

Notation "P ==> Q" := (entails P Q) (at level 90, no associativity).

Definition equiv (P Q:assert) : Prop :=
  forall s h, P s h <-> Q s h.

Notation "P <==> Q" := (equiv P Q) (at level 90, no associativity).

Lemma con_TT : forall P, P ==> (P ** TT).
red.
intros.
exists h.
exists heap.emp.
split.
apply heap.disjoint_emp.
split.
apply sym_eq.
apply heap.equal_union_emp.
split; auto.
red; auto.
Qed.

Lemma con_com : forall P Q, P ** Q ==> Q ** P.
red.
intros.
inversion_clear H as [h1].
inversion_clear H0 as [h2].
decompose [and] H; clear H.
exists h2.
exists h1.
split.
apply heap.disjoint_com; auto.
split.
apply trans_eq with (h1 +++ h2). 
auto.
apply heap.union_com.
auto.
auto.
Qed.

Axiom assert_ext: forall P Q, (P <==> Q) -> P = Q.

Lemma con_com_equiv : forall P Q, (P ** Q) = (Q ** P).
intros.
apply assert_ext.
split; intros.
apply con_com; auto.
apply con_com; auto.
Qed.

Lemma con_assoc: forall P Q R, (P ** Q) ** R ==> P ** (Q ** R).
red.
intros.
inversion_clear H.
inversion_clear H0.
decompose [and] H; clear H.
inversion_clear H1.
inversion_clear H.
decompose [and] H1; clear H1.
exists x1; exists (heap.union x2 x0).
split.
apply heap.disjoint_union.
split; auto.
apply heap.equal_union_disjoint with x2.
rewrite <-H5.
auto.
split.
rewrite H2.
rewrite H5.
apply sym_eq.
apply heap.union_assoc.
split; auto.
exists x2; exists x0.
split.
apply heap.equal_union_disjoint with x1.
assert ((x2 +++ x1) = (x1 +++ x2)).
apply heap.union_com.
apply heap.disjoint_com; auto.
rewrite H1.
rewrite <-H5; auto.
auto.
Qed.

Lemma con_assoc_equiv : forall P Q R, ((Q ** P) ** R) = (Q ** (P ** R)).
intros.
apply assert_ext.
split; intros.
apply con_assoc.
auto.
rewrite con_com_equiv.
apply con_assoc.
rewrite con_com_equiv.
apply con_assoc.
rewrite con_com_equiv.
auto.
Qed.

Lemma mp : forall P Q, Q ** (Q -* P) ==> P.
red.
intros.
red in H.
inversion_clear H.
inversion_clear H0.
decompose [and] H; clear H.
red in H4.
assert (heap.disjoint x0 x).
apply heap.disjoint_com; auto.
apply (H4 _ (conj (heap.disjoint_com _ _ H0) H1)).
rewrite H2.
apply heap.union_com; auto.
Qed.

Lemma monotony : forall (P1 P2 Q1 Q2:assert),
  forall s h,
    ((forall h', P1 s h' -> P2 s h') /\ (forall h'', Q1 s h'' -> Q2 s h'')) -> 
    ((P1 ** Q1) s h -> (P2 ** Q2) s h).
intros.
red.
inversion_clear H0.
inversion_clear H1.
decompose [and] H0; clear H0.
generalize ((proj1 H) _ H2); intro.
generalize ((proj2 H) _ H5); intro.
exists x.
exists x0.
split; auto.
Qed.

Lemma monotony': forall P1 P2 P3 P4,
 (P1 ==> P2) ->
 (P3 ==> P4) ->
 (P1 ** P3 ==> P2 ** P4).
intros.
red; intros.
inversion_clear H1.
inversion_clear H2.
exists x; exists x0; intuition.
Qed.

Lemma monotony'': forall P1 P2 P3 P4,
 (P2 ==> P1) ->
 (P3 ==> P4) ->
 (P1 -* P3 ==> P2 -* P4).
intros.
red; intros.
red; intros.
apply H0.
red in H1.
apply H1 with h'; intuition.
Qed.

Lemma adjunction : forall (P1 P2 P3:assert),
  forall s,
    (forall h, (P1 ** P2) s h -> P3 s h) ->
    (forall h, P1 s h -> (P2 -* P3) s h).
intros.
red.
intros.
apply H.
red.
exists h.
exists h'.
split; auto.
intuition.
intuition.
Qed.

Lemma adjunction' : forall (P1 P2 P3:assert),
  forall s,
    (forall h, P1 s h -> (P2 -* P3) s h) ->
       (forall h, (P1 ** P2) s h -> P3 s h).
intros.
inversion_clear H0.
inversion_clear H1.
decompose [and] H0; clear H0.
generalize (H x H2); intros.
red in H0.
eapply H0.
intuition.
apply H1; apply H3.
auto.
auto.
Qed.

Lemma imp_reg : forall P Q, P ==> Q -* (P ** Q).
red.
intros.
red.
intros.
red.
exists h.
exists h'.
split; auto.
intuition.
intuition.
Qed.

Definition emp : assert := fun s h => h = heap.emp.

Lemma con_emp: forall P, (P ** sep.emp) ==> P .
intros; red; intros.
inversion_clear H.
inversion_clear H0.
decompose [and] H; clear H.
red in H4.
subst x0.
assert (h = x).
subst h.
apply heap.equal_union_emp.
rewrite H; auto.
Qed.

Lemma con_emp': forall P, P  ==> (P ** sep.emp).
  red; intros.
  exists h; exists heap.emp.
  split.
  apply heap.disjoint_emp.
  split.
  symmetry.
  apply heap.equal_union_emp.
  split; [auto | red; auto].
Qed.

(* The mapping assertion *)
Definition mapsto e e' s h := exists p, 
    val2loc (eval e s) = p /\ h = heap.singleton p (eval e' s).

Notation "e1 '|->' e2" := (mapsto e1 e2) (at level 79, no associativity).

Lemma mapsto_con_inversion : forall l e P s h,
  ((l |-> e) ** P) s h ->
  exists n,
    val2loc (eval l s) = n /\ 
    exists h',
      h = (heap.singleton n (eval e s)) +++ h' /\
      P s h'.
  intros.
  inversion_clear H as [h''].
  inversion_clear H0 as [h'].
  decompose [and] H; clear H.
  inversion_clear H1 as [n].
  inversion_clear H.
  exists n.
  split; auto.
  exists h'.
  split; auto.
  rewrite H2.
  rewrite H3.
  auto.
Qed.

Definition cell_exists (e1: expr) : assert :=
 fun s h => exists y, (e1 |-> int_e y) s h.

Notation " e '|->_' " := (cell_exists e) (right associativity, at level 80).

Fixpoint mapstos (e:expr) (l:list expr) {struct l} : assert :=
  match l with
    nil => sep.emp
    | e1::tl => e |-> e1 ** mapstos (e +e int_e 1%Z) tl
  end.

Notation "x '|-->' l" := (mapstos x l) (at level 80).

End sep.

Notation "P ** Q" := (sep.con P Q) (at level 80) : sep_scope.
Notation "P -* Q" := (sep.imp P Q) (at level 80) : sep_scope.
Notation "P ==> Q" := (sep.entails P Q) (at level 90, no associativity) : sep_scope.
Notation "P <==> Q" := (sep.equiv P Q) (at level 90, no associativity) : sep_scope.
Notation "e1 '|->' e2" := (sep.mapsto e1 e2) (at level 79, no associativity) : sep_scope.
Notation "x '|-->' l" := (sep.mapstos x l) (at level 80) : sep_scope.

Lemma mapsto_equiv' : forall s s' h e1 e2 e3 e4,
  (e1|->e2) s' h ->
  eval e1 s' = eval e3 s ->
  eval e2 s' = eval e4 s ->
  (e3|->e4) s h.
intros.
red in H.
inversion_clear H.
inversion_clear H2.
red.
exists x.
rewrite <- H0.
rewrite <- H1.
auto.
Qed.

Lemma mapsto_equiv : forall s h e1 e2 e3 e4,
    (e1|->e2) s h ->
    eval e1 s = eval e3 s ->
    eval e2 s = eval e4 s ->
    (e3|->e4) s h.
intros.
eapply mapsto_equiv'.
apply H; auto.
auto.
auto.
Qed.

Definition inde (l:list var.v) (P:assert) :=
  forall s h,
    (forall x v, In x l -> (P s h <-> P (store.update x v s) h)).

Lemma inde_update_store : forall (P:assert) x z s h,
  inde (x::nil) P ->
  P s h ->
  P (store.update x z s) h.
  intros.
  red in H.
  generalize (H s h x z); intro.
  assert (In x (x::nil)).
  red; simpl; auto.
  tauto.
Qed.

Lemma inde_update_store' : forall (P:assert) x z s h,
  inde (x::nil) P ->
  P (store.update x z s) h ->
  P s h.
  intros.
  red in H.
  generalize (H s h x z); intro.
  assert (In x (x::nil)).
  red; simpl; auto.
  tauto.
Qed.

Lemma inde_TT : forall l, inde l TT.
  split; intros; tauto.
Qed.

Lemma inde_sep_con : forall l (P Q:assert),
  inde l P -> inde l Q ->
  inde l (P ** Q).
  unfold inde.
  split; intros.
  inversion_clear H2.
  inversion_clear H3.
  decompose [and] H2; clear H2.
  exists x0; exists x1.
  split; auto.
  generalize (H s x0 x v H1); intro.
  generalize (H0 s x1 x v H1); intro.
  tauto.
  inversion_clear H2.
  inversion_clear H3.
  decompose [and] H2; clear H2.
  exists x0; exists x1.
  split; auto.
  generalize (H s x0 x v H1); intro.
  generalize (H0 s x1 x v H1); intro.
  tauto.
Qed.

Lemma inde_sep_imp : forall l (P Q:assert),
  inde l P -> inde l Q ->
  inde l (P -* Q).
  intros.
  red.
  intros.
  split; intros.
  red in H2.
  red.
  intros.
  assert (P s h').
  red in H.
  generalize (H s h' _ v H1); intro.
  tauto.
  generalize (H2 _ (conj (proj1 H3) H5)); intro.
  red in H0.
  generalize (H0 s h'' _ v H1); intro.
  inversion_clear H7.
  apply H8; clear H9.
  apply H6.
  auto.
  red.
  intros.
  assert (P (store.update x v s) h').
  red in H.
  generalize (H s h' _ v H1); intro.
  tauto.
  generalize (H2 _ (conj (proj1 H3) H5)); intro.
  red in H0.
  generalize (H0 s h'' _ v H1); intro.
  inversion_clear H7.
  apply H9; clear H8.
  apply H6.
  auto.
Qed.

Lemma inde_mapsto : forall lst e e',
  inter (expr_var e) lst nil ->
  inter (expr_var e') lst nil ->
  inde lst (e |-> e').
  intros.
  red.
  split; intros.
  inversion_clear H2.
  inversion_clear H3.
  exists x0.
  rewrite <-(inde_expr _ _ H _ H1 s v).
  rewrite <-(inde_expr _ _ H0 _ H1 s v).
  split; auto.
  inversion_clear H2.
  inversion_clear H3.
  exists x0.
  rewrite (inde_expr _ _ H _ H1 s v).
  rewrite (inde_expr _ _ H0 _ H1 s v).
  auto.
Qed.

(* TODO: useless? *)
Lemma inde_mapsto' : forall e x,
  inde x (fun s h => exists z, (int_e e |-> int_e z) s h).
  split; intros.
  inversion_clear H0.
  exists x1.
  intuition.
  inversion_clear H0.
  exists x1.
  intuition.
Qed.

(* TODO: useless? *)
Lemma inde_mapsto'' : forall e1 e2 x,
  inde x (int_e e1 |-> int_e e2).
  split; intros; auto.
Qed.

(* fold_right : forall A B : Set, (B -> A -> A) -> A -> list B -> A *)
(* fold_right = fun (A B : Set) (f : B -> A -> A) (a0 : A) =>
	fix fold_right (l : list B) : A :=
	  match l with
	  | nil => a0
	  | b :: t => f b (fold_right t)
	  end : forall A B : Set, (B -> A -> A) -> A -> list B -> A *)
Lemma inde_mapstos : forall lst l e,
  inter (fold_right (@app var.v) nil (map expr_var lst)) l nil ->
  inter (expr_var e) l nil ->
  inde l (e |--> lst).
  induction lst; intros.
  split; intros; tauto.
  
  split; intros.
  simpl.
  simpl in H2.
  inversion_clear H2 as [h1].
  inversion_clear H3 as [h2].
  decompose [and] H2; clear H2.
  exists h1; exists h2.
  split; auto.
  split; auto.
  split.
  apply inde_update_store; auto.
  apply inde_mapsto.
  
  split; intros; try contradiction.
  simpl.
  inversion_clear H2.
  simpl in H8.
  inversion_clear H8; try contradiction.
  subst x0.
  red in H0.
  generalize (H0 x); tauto.
  
  split; intros; try contradiction.
  simpl.
  inversion_clear H2.
  simpl in H8.
  inversion_clear H8; try contradiction.
  subst x0.
  red in H.
  generalize (H x); intro.
  simpl in H2.
  inversion_clear H2.
  clear H9.
  apply H8; clear H8.
  split; auto.
  apply in_or_app.
  auto.
  
  apply inde_update_store; auto.
  apply IHlst.
  apply inter_weak.
  apply inter_nil.
  intro.
  simpl in H.
  generalize (H x); intro.
  inversion_clear H6.
  clear H9.
  apply H8.
  split; auto.
  apply in_or_app.
  tauto.
  
  simpl.
  rewrite <-app_nil_end.
  apply inter_weak.
  apply inter_nil.
  intro.
  generalize (H0 x); intro.
  tauto.
  
  apply inde_update_store' with (x:=x) (z:=v); auto.
  simpl.
  apply inde_sep_con.
  apply inde_mapsto.
  apply inter_weak.
  apply inter_nil.
  intro.
  generalize (H0 x); tauto.
  apply inter_weak.
  apply inter_nil.
  intro.
  generalize (H x); intro.
  inversion_clear H4.
  clear H6.
  apply H5.
  split; auto.
  simpl.
  apply in_or_app.
  auto.
  
  apply IHlst.
  simpl in H.
  apply inter_weak.
  apply inter_nil.
  intro.
  generalize (H x); intro.
  inversion_clear H4.
  clear H6; apply H5.
  split; auto.
  apply in_or_app.
  auto.
  apply inter_weak.
  apply inter_nil.
  intro.
  simpl in H3.
  rewrite <-app_nil_end in H3.
  generalize (H0 x); intro.
  tauto.
Qed.

