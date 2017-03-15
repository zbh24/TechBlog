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

Require Import ZArith.
Require Import EqNat.
Require Import Bool.
Require Import ZArith.
Require Import List.
Require Import Classical.
Require Import util.

Module Type MAP.
  Parameter l : Set.
  Parameter v : Set.
  Parameter h : Set.

  Parameter emp : h. (* the empty heap *)
  Parameter singleton : l -> v -> h. (* singleton heaps *)

  Parameter lookup : l -> h -> option v.
  Parameter lookup_emp : forall x, lookup x emp = None.
  Parameter lookup_singleton : forall n w, lookup n (singleton n w) = Some w.

  Parameter extensionality: forall h1 h2, (forall x, lookup x h1 = lookup x h2) -> h1 = h2.

  Parameter update : l -> v -> h -> h.
  Parameter update_singleton : forall n w w', update n w' (singleton n w) = singleton n w'.

  Parameter union : h -> h -> h.
  Notation "k '+++' m" := (union k m) (at level 69) : heap_scope.
  Open Local Scope heap_scope.

  Parameter equal_union_emp : forall h1, h1 +++ emp = h1.
  Parameter union_assoc : forall h1 h2 h3, h1 +++ (h2 +++ h3) = (h1 +++ h2) +++ h3.
  Parameter lookup_union_or: forall h1 h2 n z,
    lookup n (h1 +++ h2) = Some z ->
    lookup n h1 = Some z \/ lookup n h2 = Some z.

  Parameter lookup_update : forall x y z st, x <> y -> lookup x st = lookup x (singleton y  z +++ st).
  Parameter lookup_update' : forall x z st, lookup x (singleton x z +++ st) = Some z.
  Parameter lookup_update'' : forall x y z st,
    x <> y -> lookup x st = lookup x (update y z st).

  Parameter disjoint : h -> h -> Prop.
  Notation "k '#' m" := (disjoint k m) (at level 79) : heap_scope.

  Parameter disjoint_emp : forall h, h # emp.
  Parameter disjoint_singleton : forall x y z z', x <> y -> (singleton x z) # (singleton y z').
  Parameter disjoint_singleton' : forall x y z z', (singleton x z) # (singleton y z') -> x <> y.
  Parameter disjoint_com : forall h0 h1,  h0 # h1 -> h1 # h0.
  Parameter disjoint_update : forall n z h1 h2,  h1 # h2 -> (update n z h1) # h2.
  Parameter disjoint_union : forall h1 h2 h0,  h0 # h1 /\ h0 # h2  ->  h0 # (h1 +++ h2).
  Parameter disjoint_union' : forall h1 h2 h0,  h0 # (h1 +++ h2) -> h0 # h1 /\ h0 # h2.

  Parameter equal_union_disjoint : forall x1 x2 x0, (x1 +++ x2) # x0  ->  x1 # x0.
  (* union is not commutative in general! *)
  Parameter union_com : forall h1 h2,  h1 # h2 -> h1 +++ h2 = h2 +++ h1.

  (* TODO: rename as lookup_union_L *)
  Parameter lookup_union : forall h1 h2, h1 # h2 ->
    forall n z, lookup n h1 = Some z -> 
      lookup n (h1 +++ h2) = Some z.
  Parameter lookup_union_R : forall h1 h2, h1 # h2 ->
    forall n z, lookup n h2 = Some z -> 
      lookup n (h1 +++ h2) = Some z.
  Parameter equal_update_L : forall h1 h2, h1 # h2 ->
      forall n z z1, lookup n h1 = Some z1 ->
	update n z (h1 +++ h2) = (update n z h1) +++ h2.
  Parameter equal_update_R : forall (h1 h2:h), h1 # h2 ->
    forall (n:l) (z z2:v), lookup n h2 = Some z2 ->
      update n z (h1 +++ h2) = h1 +++ (update n z h2).
  Parameter lookup_exists_partition: forall h a b,
    lookup a h = Some b ->
    exists h'' , h = (singleton a b) +++ h'' /\ (singleton a b) # h''.
  Parameter disjoint_comp : forall h'1 h1 h2 h'2,
    h1 # h'1 -> h1 # h2 -> h'1 # h'2 ->
    h'1 +++ h'2 = h1 +++ h2 ->
    exists h', h'1 # h' /\ h2 = (h' +++ h'1).

  Parameter dif : h -> l -> h.
  Notation "k '---' l" := (dif k l) (at level 69) : heap_scope.

  Parameter dif_singleton_emp: forall a b, (singleton a b) --- a = emp.
  Parameter dif_union: forall h1 h2 a, (h1 +++ h2) --- a = (h1 --- a) +++ (h2 --- a).
  Parameter dif_disjoint: forall h a b, h # (singleton a b) -> (h --- a) = h.
  Parameter dif_disjoint': forall h1 h2 l, h1 # h2 -> (h1 --- l) # (h2 --- l).
  Parameter lookup_dif : forall w st, lookup w (st --- w) = None.
  Parameter lookup_dif' : forall st x y, x <> y -> lookup x (st --- y) = lookup x st.

End MAP.

Module Type ELEM.
  Parameter elem : Set.
End ELEM.

Require OrderedType.

Module Type OrderedTypeExt.

  Parameter t : Set.

  Parameter eq : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.

  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.

  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

  Parameter compare : forall x y : t, OrderedType.Compare lt eq x y.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.

  Axiom eq_ext : forall x y : t, eq x y -> x = y.

End OrderedTypeExt.

Module map (A: OrderedTypeExt) (E : ELEM) : MAP 
  with Definition l := A.t
    with Definition v := E.elem.

  Definition l := A.t.
  Definition v := E.elem.

  (* lemmas about the order type *)

  Notation "a < b" := (A.lt a b) : addr_scope.

  Open Local Scope addr_scope.
  Delimit Scope addr_scope with addr_scope.

  Module otf := OrderedType.OrderedTypeFacts A.
  
  Definition mygt a b := (b < a)%addr_scope.
  Notation "a > b" := (mygt a b) : addr_scope.
  
  Definition myle x y := x < y \/ A.eq x y.
  Notation "a <= b" := (myle a b) : addr_scope.
  
  Definition myge a b := (b <= a)%addr_scope.
  Notation "a >= b" := (myge a b) : addr_scope.

  Lemma mytrichotomy : forall x y : l, (x < y \/ x = y \/ x > y)%addr_scope.
    intros.
    generalize (A.compare x y); intro.
    destruct H; auto.
    right; left.
    apply A.eq_ext; auto.
  Qed.
  
  Lemma gt_neq : forall a b : l, (a < b -> a <> b)%addr_scope.
    intros.
    generalize (otf.gt_not_eq H); intro.
    swap H0.
    subst a.
    auto.
  Qed.
  
  Lemma mylt_neq : forall a b : l, (b < a -> a <> b)%addr_scope.
    intros.
    generalize (otf.gt_not_eq H); intro.
    swap H0.
    subst b.
    auto.
  Qed.

  Lemma myleq_neq_lt : forall a b : l, (a <= b -> a <> b -> a < b)%addr_scope.
    intros.
    inversion_clear H.
    auto.
    generalize (A.eq_ext _ _ H1); intro.
    subst a.
    tauto.
  Qed.
  
  Lemma myle_ge_eq : forall a b:l, (a <= b -> b <= a -> a = b)%addr_scope.
    intros.
    red in H; red in H0; inversion_clear H; inversion_clear H0.
    apply otf.lt_not_gt in H1.
    tauto.
    apply A.eq_ext; auto.
    apply A.eq_ext; auto.
    apply A.eq_ext; auto.
  Qed.

  Lemma mylt_trans2 : forall n m p : l, (n <= m -> m < p -> n < p)%addr_scope.
    intros.
    inversion_clear H.
    apply A.lt_trans with m; auto.
    apply A.eq_ext in H1.
    subst n.
    auto.
  Qed.

  Lemma myle_eq_lt : forall a b, (a <= b -> a = b \/ a < b)%addr_scope.
    inversion_clear 1; auto.
    left; apply A.eq_ext; auto.
  Qed.
  
  Definition addr_lt (x y:l) := 
    match A.compare x y with
      | OrderedType.LT _ => true
      | _ => false
    end.

  Lemma addr_lt_false' : forall n m : l, (n >= m -> addr_lt n m = false)%addr_scope.
    intros.
    unfold addr_lt.
    destruct (A.compare n m); auto.
    red in H.
    red in H.
    inversion_clear H.
    generalize (otf.lt_not_gt l0); intro.
    tauto.
    apply A.eq_ext in H0.
    subst m.
    generalize (otf.lt_antirefl l0); tauto.
  Qed.

  Lemma addr_lt_classic : forall n m : l, addr_lt n m = true \/ addr_lt n m = false.
    intros.
    generalize (otf.lt_dec n m); intro.
    inversion_clear H.
    left.
    unfold addr_lt.
    destruct (A.compare n m); auto.
    apply A.eq_ext in e.
    subst m.
    generalize (otf.lt_antirefl H0); tauto.
    generalize (otf.lt_not_gt l0); intro.
    tauto.
    right.
    unfold addr_lt.
    destruct (A.compare n m); auto.
    tauto.
  Qed.

  Lemma addr_lt_false : forall n m : l, addr_lt n m = false -> (n >= m)%addr_scope.
    intros.
    unfold addr_lt in H.
    destruct (A.compare n m).
    discriminate.
    red.
    red.
    auto.
    red.
    red.
    auto.
  Qed.
    
  Lemma addr_lt_true : forall n m : l, addr_lt n m = true -> (n < m)%addr_scope.
    intros.
    unfold addr_lt in H.
    destruct (A.compare n m).
    auto.
    discriminate.
    discriminate.
  Qed.

  Lemma addr_lt_true' : forall n m : l, (n < m)%addr_scope -> addr_lt n m = true.
    intros.
    unfold addr_lt.
    destruct (A.compare n m).
    auto.
    apply A.eq_ext in e.
    subst m.
    generalize (otf.lt_not_gt H); tauto.
    generalize (otf.lt_not_gt H); tauto.
  Qed.

  Lemma addr_lt_irrefl : forall n : l, addr_lt n n = false.
    intros.
    unfold addr_lt.
    destruct (A.compare n n).
    generalize (otf.lt_not_gt l0); tauto.
    auto.
    auto.
  Qed.
    
  Lemma addr_lt_assym : forall n m : l, addr_lt n m = true -> addr_lt m n = false.
    unfold addr_lt.
    do 2 intro.
    destruct (A.compare n m); destruct (A.compare m n); auto.
    intros.
    generalize (otf.lt_not_gt l0); intro.
    tauto.
  Qed.

  Definition beq_addr (x y:l) := 
    match (A.compare x y) with
      | OrderedType.EQ _ => true
      | _ => false
    end.

  Lemma beq_dif_false_addr : forall n m : l, n <> m -> beq_addr n m = false.
    intros.
    unfold beq_addr.
    destruct (A.compare n m); auto.
    apply A.eq_ext in e.
    subst m.
    tauto.
  Qed.

  Lemma beq_addr_refl : forall n : l, true = beq_addr n n.
    intros.
    unfold beq_addr.
    destruct (A.compare n n); auto.
    generalize (otf.lt_antirefl l0); tauto.
    generalize (otf.lt_antirefl l0); tauto.
  Qed.
    
  Lemma beq_addr_classic : forall a b : l, beq_addr a b = true \/ beq_addr a b = false.
    intros.
    unfold beq_addr.
    destruct (A.compare a b); auto.
  Qed.

  Lemma beq_addr_true : forall x y : l, beq_addr x y = true -> x = y.
    do 2 intro.
    unfold beq_addr.
    destruct (A.compare x y); intros; try discriminate.
    apply A.eq_ext; auto.
  Qed.
    
  Lemma beq_addr_false : forall a b : l, beq_addr a b = false -> a <> b.
    do 2 intro.
    unfold beq_addr.
    destruct (A.compare a b); intros; try discriminate.
    assert ( b <> a ).
    apply mylt_neq.
    auto.
    auto.
    apply mylt_neq.
    auto.
  Qed.

  Lemma beq_addr_com : forall n m : l, beq_addr n m = beq_addr m n.
    unfold beq_addr.
    do 2 intro.
    destruct (A.compare n m); destruct (A.compare m n); intros; try discriminate||auto.
    apply A.eq_ext in e.
    subst m.
    generalize (otf.lt_antirefl l0); tauto.
    apply A.eq_ext in e.
    subst m.
    generalize (otf.lt_antirefl l0); tauto.
    apply A.eq_ext in e.
    subst m.
    generalize (otf.lt_antirefl l0); tauto.
    apply A.eq_ext in e.
    subst m.
    generalize (otf.lt_antirefl l0); tauto.
  Qed.

  (*
   * definition of ordered sets
   *)

  (* strict lower bound of a list *)
  Fixpoint lb (loc:l) (he:list l) {struct he} : Prop :=
    match he with
      | nil => True
      | hd::tl => loc < hd /\ lb loc tl
    end.

  Lemma lb_notin : forall k a, lb a k -> ~ In a k.
    induction k; intros; auto.
    simpl in H.
    intro.
    simpl in H0.
    inversion_clear H0.
    subst a0.
    inversion_clear H.
    generalize (otf.lt_antirefl H0); tauto.
    inversion_clear H.
    generalize (IHk _ H2); tauto.
  Qed.      

  Lemma lb_notin' : forall k a, In a k -> ~ lb a k.
    induction k; intros; auto.
    simpl in H.
    inversion_clear H.
    subst a0.
    simpl.
    intro.
    inversion_clear H.
    generalize (otf.lt_antirefl H0); tauto.
    intro.
    simpl in H.
    inversion_clear H.
    generalize (IHk _ H0); auto.
  Qed.

  Lemma lb_In_uneq: forall k a c, In a k -> lb c k -> beq_addr a c = false.
    induction k; intros; auto.
    simpl in H.
    tauto.
    simpl in H.
    inversion_clear H.
    subst a0.
    simpl in H0.
    inversion_clear H0.
    apply beq_dif_false_addr.
    red.
    intros.
    subst a.
    generalize (otf.lt_antirefl H); tauto.
    apply IHk.
    auto.
    simpl in H0.
    tauto.
  Qed.

  Lemma lb_trans: forall k n m , lb m k -> n < m -> lb n k.
    induction k; intros; auto.
    simpl in H.
    simpl.
    split.
    apply A.lt_trans with m.
    auto.
    tauto.
    apply IHk with m.
    tauto.
    auto.
  Qed.

  Fixpoint set (locs:list l) : Prop :=
    match locs with
      nil => True
      | hd::tl => lb hd tl /\ set tl
    end.

  (*
   * definition of heaps
   *)
  
  Definition dom (k:list (l*v)) := map (fun x => fst x) k.

  Inductive h' : Set := mk_h : forall lst, set (dom lst) -> h'.
  Definition h := h'.

  Definition lst := fun k:h => let (lst, _) := k in lst.
  Definition prf := fun k:h => 
    let (lst, va) as h return (set (dom (lst h))) := k in va.

  (*
   * empty heap
   *)

  Definition set_nil : set nil.
    red.
    auto.
  Qed.

  Definition emp := mk_h nil set_nil.

  (*
   * singleton heap
   *)

  Definition set_singleton : forall n v, set (dom ((n,v)::nil)).
    intros.
    simpl.
    auto.
  Qed.

  Definition singleton := fun (n:l) (w:v) => 
    mk_h ((n, w)::nil) (set_singleton n w).

  (***********
     lookup 
  ***********)
  
  (* TODO: optimize using the fact that domains are ordered *)
  Fixpoint lookup' (n:l) (k:list (l*v)) {struct k} : option v :=
    match k with
      nil => None
      | hd::tl => match beq_addr n (fst hd) with
		    true => Some (snd hd)
		    | false => lookup' n tl
                  end
    end.

  Definition lookup n k := lookup' n (lst k).

  Lemma lookup_emp : forall x, lookup x emp = None.
    intros.
    unfold lookup.
    simpl.
    reflexivity.
  Qed.

  Lemma lookup_singleton : forall n w, lookup n (singleton n w) = Some w.
    intros.
    unfold singleton.
    unfold lookup.
    simpl.
    rewrite <- beq_addr_refl.
    auto.
  Qed.

  Lemma lookup'_In : forall (k:list (l*v)) (n:l) (z:v), 
    lookup' n k = Some z -> In n (dom k).
    induction k; simpl; intros.
    discriminate.
    destruct a as [a b].
    simpl in H.
    simpl.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    generalize (beq_addr_true _ _ H0); intro.
    subst a.
    auto.
    right.
    apply IHk with z.
    rewrite H0 in H.
    auto.
  Qed.

  Lemma lookup_not_In: forall h x, ~ In x (dom (lst h)) -> lookup x h = None.
    destruct h0 as [l0 s0].
    simpl.
    unfold lookup.
    simpl.
    induction l0; intros; simpl; auto.
    destruct a.
    simpl.
    assert (~ (x = l1)).
    simpl in H.
    simpl in s0.
    intuition.
    rewrite (beq_dif_false_addr _ _ H0).
    apply IHl0.
    simpl in s0.
    tauto.
    simpl in H.
    tauto.
  Qed.

  (*******************
    heap equivalence
  ********************)

  Definition equal (h1: h) (h2: h) := (lst h1) = (lst h2).

  Notation "k '===' m" := (equal k m) (at level 79) : heap_scope.

  Open Local Scope heap_scope.

  Lemma equal_ext: forall h1 h2, h1 === h2 -> h1 = h2.
    destruct h1 as [lst1  prf1].
    destruct h2 as [lst2  prf2].
    unfold equal.
    simpl.
    intros.
    subst lst1.
    rewrite (proof_irrelevance _ prf1 prf2).
    auto.
  Qed.

  Lemma equal_ext': forall h1 h2, h1 = h2 -> h1 === h2.
    unfold equal.
    intros; subst h2; auto.
  Qed.

  Lemma extensionality: forall h1 h2, 
    (forall x, lookup x h1 = lookup x h2) -> h1 = h2.
    intros.
    apply equal_ext.
    generalize H; clear H.
    destruct h1 as [lst1 set1].
    destruct h2 as [lst2 set2].
    simpl.
    generalize lst1 set1 lst2 set2; clear lst1 set1 lst2 set2.
    induction lst1.
    simpl; intros.
    destruct lst2.
    assert (set1 = set2).
    apply proof_irrelevance.
    rewrite H0; apply equal_ext'; auto.
    induction p.
    generalize (H a); intros.
    unfold lookup in H0.
    simpl in H0.
    rewrite <- beq_addr_refl in H0.
    inversion H0.
    induction a; unfold lookup; simpl; intros.
    unfold equal; simpl.
    assert (exists lst2', lst2 = (a,b)::lst2').
    destruct lst2.
    simpl in H.
    generalize (H a); intro X; rewrite <- beq_addr_refl in X; inversion X.
    destruct p as [a' b'].
    assert (forall x y, x < y \/ x = y \/ x > y).
    intros.
    apply mytrichotomy.
    generalize (H a'); intros.
    generalize (H0 a' a); intro X; inversion_clear X.
    generalize (beq_dif_false_addr a' a).
    intro.
    rewrite H3 in H1.
    simpl in H1.
    rewrite <- beq_addr_refl in H1.
    generalize (lookup_not_In (mk_h lst1 (proj2 set1) ) a'); intro.
    unfold lookup in H4; simpl in H4.
    assert (~ In a' (dom lst1)).
    unfold dom.
    red; intros.
    generalize (lb_notin' _ _ H5); intro. 
    generalize (lb_trans _ _ _ (proj1 set1) H2); intro; contradiction.
    rewrite (H4 H5) in H1.
    discriminate.
    apply gt_neq.
    auto.
    inversion_clear H2.
    subst a'.
    rewrite <- beq_addr_refl in H1.
    simpl in H1.
    rewrite <- beq_addr_refl in H1.
    injection H1; intro; subst b'.
    exists lst2.
    auto.
    generalize (H a); intro.
    rewrite <-beq_addr_refl in H2.
    generalize (beq_dif_false_addr a a').
    intro.
    simpl in H2.
    rewrite H4 in H2.
    assert (lookup' a lst2 = Some b).
    auto.

    (* exhibit a proof of a' < a to make a contradiction *)

    generalize (lookup'_In _ _ _ (sym_eq H2)); intro.
    simpl in set2.
    generalize (proj1 set2); intro.
    red in H3.
    generalize (lb_trans _ _ _ H7 H3); intro.
    generalize (lb_notin' _ _ H6); intro.
    contradiction.
    apply gt_neq.
    red in H3.
    auto.
    inversion_clear H0 as [lst2'].
    subst lst2.
    simpl in set2.
    assert ((forall x : l,
      lookup x (mk_h lst1 (proj2 set1)) = lookup x (mk_h lst2' (proj2 set2)))).
    intros.
    generalize (H x); intro.
    unfold lookup; simpl.
    generalize (beq_addr_classic x a); intro X; inversion_clear X.
    generalize (beq_addr_true _ _ H1); intro; subst x.
    generalize lookup_not_In; intro.
    unfold lookup in H2.
    generalize (H2 (mk_h lst1 (proj2 set1)) a); intro X; simpl in X.
    rewrite X; clear X.
    generalize (H2 (mk_h lst2' (proj2 set2)) a); intro X; simpl in X.
    rewrite X; clear X.
    auto.
    red; intros.
    generalize (lb_notin (dom lst2') a); intro.
    generalize (H4 (proj1 set2)); intros.
    contradiction.
    intro.
    generalize (lb_notin (dom lst1) a); intro.
    generalize (H4 (proj1 set1)); intros.
    contradiction.
    rewrite H1 in H0.
    simpl in H0.
    rewrite H1 in H0.
    auto.
    unfold equal in IHlst1.
    simpl in IHlst1.
    rewrite (IHlst1 (proj2 set1) lst2' (proj2 set2) H0).
    auto.
  Qed.

  (***********
      update
   ***********)

  (* TODO: optimize the function (using the fact that the domain is ordered) *)
  Fixpoint update' (n:l) (w:v) (k:list (l*v)) {struct k} : list (l*v) :=
    match k with
      nil => k
      | hd::tl => match beq_addr n (fst hd) with
		    true => (fst hd, w)::tl 
		    | false => hd::(update' n w tl)
		  end
    end.
  
  Lemma lb_update : forall (n:l) (k:list (l*v)), lb n (dom k) -> 
    forall (m:l) (w:v), lb n (dom (update' m w k)).
    induction k; simpl; intros; auto.
    destruct a as [a b].
    simpl.
    simpl in H.
    generalize (beq_addr_classic m a); intro X; inversion_clear X.
    generalize (beq_addr_true m a H0); intros.
    subst a.
    rewrite <- beq_addr_refl.
    simpl.
    auto.
    rewrite H0.
    simpl.
    split.
    tauto.
    apply IHk.
    tauto.
  Qed.

  Lemma set_update: forall (k:list (l*v)), set (dom k) -> 
    forall (n:l) (w:v), set (dom (update' n w k)).
    induction k; auto.
    destruct a as [a b]; simpl; intros.
    inversion_clear H.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    generalize (beq_addr_true n a H); intros.
    subst a.
    rewrite <- beq_addr_refl.
    simpl.
    auto.
    rewrite H.
    simpl.
    split; auto.
    apply lb_update.
    auto.
  Qed.

  Definition update (n:l) (w:v) (k:h) := mk_h (update' n w (lst k)) (set_update (lst k) (prf k) n w).

  Lemma lookup'_update' : forall (k:list (l*v)) (x y:l) (z:v), x <> y -> 
    lookup' x k = lookup' x (update' y z k).
    induction k; auto.
    destruct a as [a b]; simpl; intros.
    generalize (beq_addr_classic x a); intro X; inversion_clear X.
    generalize (beq_addr_classic y a); intro X; inversion_clear X.
    generalize (beq_addr_true _ _ H0); intro; subst x.
    generalize (beq_addr_true _ _ H1); intro; subst y.
    tauto.
    rewrite H0; rewrite H1.
    simpl.
    rewrite H0.
    auto.
    generalize (beq_addr_classic y a); intro X; inversion_clear X.
    rewrite H0; rewrite H1.
    simpl.
    rewrite H0.
    auto.
    rewrite H0; rewrite H1.
    simpl.
    rewrite H0.
    auto.
  Qed.

  Lemma lookup_update'' : forall x y z st,
    x <> y -> lookup x st = lookup x (update y z st).
    intros.
    unfold lookup.
    unfold update.
    simpl.
    apply lookup'_update'.
    auto.
  Qed.

  Lemma update_dom : forall (k:h) (n:l) (z:v),
    dom (lst (update n z k)) = dom (lst k).
    destruct k as [k Hk].
    induction k; auto.
    destruct a as [a b]; simpl; intros.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    generalize (beq_addr_true _ _ H); intro.
    subst a.
    rewrite <- beq_addr_refl.
    auto.
    rewrite H.
    simpl.
    simpl in IHk.
    rewrite IHk; auto.
    exact (proj2 Hk).
  Qed.
    
  Lemma update_singleton : forall (n:l) (w w':v),
    update n w' (singleton n w) = singleton n w'.
    intros.
    apply equal_ext.
    unfold equal.
    simpl.
    rewrite <- beq_addr_refl.
    auto.
  Qed.

  (******************
    element addition
  *******************)

  Fixpoint add_lst (n:l) (w:v) (lst:list (l*v)) {struct lst}: list (l*v) :=
    match lst with
      nil => (n,w)::nil
      | (n',w')::tl => match addr_lt n' n with
                         true => (n',w') :: (add_lst n w tl)
                         | false => match beq_addr n' n with
                                      true => (n',w) :: tl
                                      | false => (n,w) :: (n',w')::tl
                                    end
		       end
    end.

  Lemma lb_add_lst : forall (k:list (l*v)) (n:l), lb n (dom k) -> 
    forall m, n < m -> forall w, lb n (dom (add_lst m w k)).
    induction k; intros; simpl.
    auto.
    induction a.
    simpl in H.
    inversion_clear H.
    generalize (beq_addr_classic a m); intro X; inversion_clear X. 
    rewrite H.
    rewrite addr_lt_false'.
    simpl.
    auto.
    generalize (beq_addr_true a m H); intros.
    subst m.
    red.
    red.
    auto.
    generalize (addr_lt_classic a m); intro X; inversion_clear X. 
    rewrite H3.
    simpl.
    split; auto.
    rewrite addr_lt_false'.
    rewrite H.
    simpl.
    auto.
    apply addr_lt_false.
    auto.
  Qed.

  Lemma add_lst_lb: forall k a b, lb a (dom k) -> add_lst a b k = (a, b)::k.
    induction k; simpl; intros; auto.
    destruct a.
    simpl in H.
    inversion_clear H.
    rewrite addr_lt_false'.
    rewrite beq_dif_false_addr.
    auto.
    apply mylt_neq.
    auto.
    red.
    red.
    auto.
  Qed.

  Lemma set_add : forall lst, set (dom lst) -> 
    forall n w, set (dom (add_lst n w lst)).
    induction lst0.
    simpl; auto.
    induction a; simpl; intros.
    inversion_clear H.
    generalize (beq_addr_classic a n); intro X; inversion_clear X. 
    rewrite H.
    generalize (addr_lt_classic a n); intro X; inversion_clear X. 
    generalize (addr_lt_true a n H2); intros.
    rewrite addr_lt_true'.
    simpl.
    split.
    generalize (lb_add_lst lst0 a H0 _ H3 w); intro.
    auto.
    auto.
    auto.
    rewrite addr_lt_false'.
    simpl.
    auto.
    generalize (beq_addr_true _ _ H); intro.
    red.
    red.
    subst n.
    auto.
    generalize (addr_lt_classic a n); intro X; inversion_clear X. 
    rewrite H2.
    simpl.
    split.
    generalize (lb_add_lst lst0 a H0 n); intro.
    assert (a < n).
    apply addr_lt_true.
    auto.
    generalize (H3 H4 w); auto.
    auto.
    rewrite addr_lt_false'.
    rewrite H.
    simpl.
    split; auto.
    split; auto.
    generalize (addr_lt_false a n H2); intro.
    generalize (beq_addr_false _ _ H); intro.
    apply myleq_neq_lt.
    auto.
    auto.
    eapply lb_trans.
    apply H0.
    generalize (addr_lt_false a n H2); intro.
    generalize (beq_addr_false _ _ H); intro.
    apply myleq_neq_lt.
    auto.
    auto.
    apply addr_lt_false.
    auto.
  Qed.

  Lemma In_dom_add_lst: forall k a b, In a (dom (add_lst a b k)).
    induction k.
    simpl.
    auto.
    destruct a as [a b]; simpl; intros.
    generalize (addr_lt_classic a a0); intro X; inversion_clear X.
    rewrite H.
    simpl.
    auto.
    rewrite H.
    generalize (beq_addr_classic a a0); intro X; inversion_clear X.
    generalize (beq_addr_true _ _ H0); intro.
    subst a0.
    rewrite <- beq_addr_refl.
    simpl.
    auto.
    rewrite H0.
    simpl.
    auto.
  Qed.
  
  Lemma In_dom_add_lst': forall k x a b, In x (dom k) -> 
    In x (dom (add_lst a b k)).
    induction k.
    simpl; tauto.
    induction a as [a b]; simpl; intros.
    inversion_clear H.
    subst x.
    generalize (addr_lt_classic a a0); intro X; inversion_clear X.
    rewrite H.
    simpl; auto.
    rewrite H.
    generalize (beq_addr_classic a a0); intro X; inversion_clear X.
    generalize (beq_addr_true _ _ H0); intro.
    subst a0.
    rewrite <- beq_addr_refl.
    simpl; auto.
    rewrite H0.
    simpl; auto.
    generalize (addr_lt_classic a a0); intro X; inversion_clear X.
    rewrite H.
    simpl; auto.
    rewrite H.
    generalize (beq_addr_classic a a0); intro X; inversion_clear X.
    generalize (beq_addr_true _ _ H1); intro.
    subst a0.
    rewrite <- beq_addr_refl.
    simpl; auto.
    rewrite H1.
    simpl; auto.
  Qed.

  Lemma add_lst'_In_dom: forall k x a b, In x (dom (add_lst a b k)) -> x = a \/ In x (dom k).
    induction k.
    simpl; intuition.
    induction a as [a b]; simpl; intros.
    generalize (addr_lt_classic a a0); intro X; inversion_clear X.
    rewrite H0 in H.
    simpl in H.
    inversion_clear H; auto.
    generalize (IHk _ _ _ H1); intro X; inversion_clear X; auto.
    rewrite H0 in H.
    generalize (beq_addr_classic a a0); intro X; inversion_clear X.
    rewrite H1 in H.
    simpl in H.
    inversion_clear H; auto.
    rewrite H1 in H.
    simpl in H.
    intuition.
  Qed.

  Lemma In_dom_add_lst2: forall k n w n', n <> n' -> 
    In n' (dom (add_lst n w k)) -> In n' (dom k).
    intros.
    generalize (add_lst'_In_dom _ _ _ _ H0); intro.
    inversion_clear H1; auto.
    subst n.
    tauto.
  Qed.

  Lemma add_lst_add_lst': forall k n w' w, add_lst n w (add_lst n w' k) = add_lst n w k.
    induction k.
    simpl.
    intros.
    rewrite addr_lt_irrefl.
    rewrite <- beq_addr_refl.
    auto.
    induction a as [a b]; simpl; intros.
    generalize (addr_lt_classic a n); intro X; inversion_clear X. 
    rewrite H.
    simpl.
    rewrite H.
    rewrite IHk.
    auto.
    rewrite H.
    generalize (beq_addr_classic a n); intro X; inversion_clear X. 
    rewrite H0.
    simpl.
    rewrite H.
    rewrite H0.
    auto.
    rewrite H0.
    simpl.
    rewrite addr_lt_irrefl.
    rewrite <- beq_addr_refl.
    auto.
  Qed.

  Lemma add_lst_add_lst: forall k n' w' n w, n' <> n -> 
    add_lst n w (add_lst n' w' k) = add_lst n' w' (add_lst n w k).
    induction k; simpl; intros.
    generalize (addr_lt_classic n' n); intro X; inversion_clear X. 
    rewrite H0.
    generalize (addr_lt_assym _ _ H0); intro.
    rewrite H1.
    generalize (beq_dif_false_addr _ _ H); intro.
    rewrite beq_addr_com.
    rewrite H2.
    auto.
    rewrite H0.
    generalize (beq_dif_false_addr _ _ H); intro.
    rewrite H1.
    generalize (addr_lt_classic n n'); intro X; inversion_clear X. 
    rewrite H2.
    auto.
    generalize (addr_lt_false _ _ H0); intros.
    generalize (addr_lt_false _ _ H2); intros.
    assert (n' = n).
    apply myle_ge_eq; auto.
    subst n.
    tauto.
    induction a as [a b]; simpl; intros.
    generalize (addr_lt_classic a n); intro X; inversion_clear X. 
    rewrite H0.
    generalize (addr_lt_classic a n'); intro X; inversion_clear X. 
    rewrite H1.
    simpl.
    rewrite H0; rewrite H1.
    rewrite IHk; auto.
    rewrite H1.
    generalize (beq_addr_classic a n'); intro X; inversion_clear X. 
    rewrite H2.
    simpl.
    rewrite H0; rewrite H1; rewrite H2.
    auto.
    rewrite H2.
    simpl.
    generalize (addr_lt_false _ _ H1); intros.
    generalize (addr_lt_true _ _ H0); intros.
    assert (n' < n).
    apply mylt_trans2 with a; auto.
    rewrite (addr_lt_true' _ _ H5).
    rewrite H0; rewrite H1; rewrite H2.
    auto.
    generalize (addr_lt_classic a n'); intro X; inversion_clear X. 
    rewrite H1.
    rewrite H0.
    generalize (beq_addr_classic a n); intro X; inversion_clear X. 
    rewrite H2.
    simpl.
    rewrite H0; rewrite H1; rewrite H2.
    auto.
    simpl.
    rewrite H0; rewrite H2.
    simpl.
    generalize (addr_lt_false _ _ H0); intros.
    generalize (addr_lt_true _ _ H1); intros.
    assert (n < n').
    apply mylt_trans2 with a; auto.
    rewrite (addr_lt_true' _ _ H5).
    rewrite H1.
    auto.
    rewrite H0; rewrite H1.
    generalize (beq_addr_classic a n'); intro X; inversion_clear X. 
    generalize (beq_addr_classic a n); intro X; inversion_clear X. 
    rewrite <- (beq_addr_true _ _ H2) in H.
    rewrite <- (beq_addr_true _ _ H3) in H.
    tauto.
    rewrite H2; rewrite H3.
    simpl.
    rewrite H0; rewrite H1; rewrite H2; rewrite H3.
    generalize (addr_lt_classic n n'); intro X; inversion_clear X. 
    rewrite H4.
    auto.
    generalize (beq_addr_true _ _ H2); intro; subst a.
    clear H2.
    generalize (addr_lt_false _ _ H4); intros.
    generalize (addr_lt_false _ _ H0); intros.
    assert (n' = n).
    apply myle_ge_eq; auto.
    subst n'.
    tauto.
    generalize (beq_addr_classic a n); intro X; inversion_clear X. 
    generalize (beq_addr_true _ _ H3); intro; subst a.
    rewrite H2.
    rewrite <-beq_addr_refl.
    simpl.
    generalize (addr_lt_false _ _ H1); intro.
    assert (n' = n \/ n' < n).
    apply myle_eq_lt; auto.
    inversion_clear H5.
    subst n'.
    tauto.
    generalize (addr_lt_true' _ _ H6); intro.
    rewrite H5; rewrite H0.
    rewrite <- beq_addr_refl.
    rewrite H1; rewrite H2.
    auto.
    rewrite H2; rewrite H3.
    simpl.
    generalize (addr_lt_classic n' n); intro X; inversion_clear X. 
    rewrite H4; rewrite H0.
    generalize (addr_lt_assym _ _ H4); intro.
    rewrite H5.
    generalize (beq_dif_false_addr _ _ H); intro.
    rewrite (beq_addr_com n).
    rewrite H6; rewrite H3.
    auto.
    rewrite H4.
    generalize (beq_dif_false_addr _ _ H); intro.
    rewrite H5.
    generalize (addr_lt_classic n n'); intro X; inversion_clear X. 
    rewrite H6; rewrite H2; rewrite H1.
    auto.
    generalize (addr_lt_false _ _ H4); intros.
    generalize (addr_lt_false _ _ H6); intros.
    assert (n' = n).
    auto.
    auto.
    apply myle_ge_eq.
    auto.
    auto.
    subst n'.
    tauto.
  Qed.
 
  Lemma update_add_lst: forall k n w w', update' n w (add_lst n w' k) = add_lst n w k.
    induction k.
    simpl; intros.
    rewrite <- beq_addr_refl.
    auto.
    induction a; simpl.
    intros.
    generalize (addr_lt_classic a n); intro X; inversion_clear X.
    rewrite H.
    simpl.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    generalize (beq_addr_true _ _ H0); intro.
    generalize (addr_lt_true _ _ H); intro.
    subst a.
    generalize (otf.lt_antirefl H2); tauto.
    rewrite H0.
    rewrite IHk.
    auto.
    rewrite H.
    generalize (beq_addr_classic a n); intro X; inversion_clear X.
    rewrite H0.
    simpl.
    rewrite beq_addr_com.
    rewrite H0.
    auto.
    rewrite H0.
    simpl.
    rewrite <- beq_addr_refl.
    auto.
  Qed.

  Lemma update_add_lst': forall k n n' w w', n' <> n -> update' n w (add_lst n' w' k) = add_lst n' w' (update' n w k).
    induction k.
    simpl.
    intros.
    rewrite beq_addr_com.
    rewrite (beq_dif_false_addr _ _ H).
    auto.
    induction a; simpl; intros.
    generalize (addr_lt_classic a n'); intro X; inversion_clear X.
    rewrite H0.
    simpl.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    rewrite H1.
    simpl.
    rewrite H0.
    auto.
    rewrite H1.
    simpl.
    rewrite H0.
    rewrite IHk.
    auto.
    auto.
    rewrite H0.
    generalize (beq_addr_classic a n'); intro X; inversion_clear X.
    rewrite H1.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    rewrite (beq_addr_true n a H2) in H; rewrite (beq_addr_true _ _ H1) in H; tauto.
    rewrite H2.
    simpl.
    rewrite H2.
    rewrite H0.
    rewrite H1.
    auto.
    rewrite H1.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    rewrite H2.
    simpl.
    rewrite beq_addr_com.
    rewrite (beq_dif_false_addr _ _ H).
    rewrite H2.
    rewrite H0.
    rewrite H1.
    auto.
    rewrite H2.
    simpl.
    rewrite beq_addr_com.
    rewrite (beq_dif_false_addr _ _ H).
    rewrite H2.
    rewrite H0.
    rewrite H1.
    auto.
  Qed.

  Lemma lookup'_add_lst : forall k n w, lookup' n (add_lst n w k) = Some w.
    induction k.
    simpl.
    intros.
    rewrite <- beq_addr_refl; auto.
    induction a.
    simpl.
    intros.
    generalize (addr_lt_classic a n); intro X; inversion_clear X.
    rewrite H.
    simpl.
    generalize (addr_lt_true a n H); intros.
    assert (n <> a).
    apply mylt_neq.
    auto.
    rewrite (beq_dif_false_addr n a H1).
    apply IHk.
    rewrite H.
    generalize (beq_addr_classic a n); intro X; inversion_clear X.
    rewrite H0.
    simpl.
    rewrite beq_addr_com; rewrite H0; auto.
    rewrite H0.
    simpl.
    rewrite <- beq_addr_refl; auto.
  Qed.

  Lemma lookup'_add_lst' : forall k n w n' , n <> n' -> lookup' n' (add_lst n w k) = lookup' n' k.
    induction k.
    simpl.
    intros.
    rewrite beq_addr_com.
    rewrite (beq_dif_false_addr n n' H); auto.
    induction a; simpl; intros.
    generalize (addr_lt_classic a n); intro X; inversion_clear X.
    rewrite H0.
    simpl.
    generalize (beq_addr_classic n' a); intro X; inversion_clear X.
    rewrite H1.
    auto.
    rewrite H1.
    apply IHk.
    auto.
    rewrite H0.
    generalize (beq_addr_classic a n); intro X; inversion_clear X.
    rewrite H1.
    generalize (beq_addr_classic n' a); intro X; inversion_clear X.
    rewrite <- (beq_addr_true _ _ H1) in H; rewrite <- (beq_addr_true _ _ H2) in H.
    tauto.
    rewrite H2.
    simpl.
    rewrite H2.
    auto.
    rewrite H1.
    generalize (beq_addr_classic n' a); intro X; inversion_clear X.
    rewrite H2.
    simpl.
    rewrite beq_addr_com.
    rewrite (beq_dif_false_addr n n' H).
    rewrite H2.
    auto.
    simpl.
    rewrite beq_addr_com.
    rewrite (beq_dif_false_addr n n' H).
    rewrite H2.
    auto.
  Qed.

  (************
    heap union
  *************)

  Fixpoint app' (h1 h2:list (l*v)) {struct h1} : list (l*v) :=
    match h1 with
      nil => h2
      | hd::tl => 
	add_lst (fst hd) (snd hd) (app' tl h2)
    end.

  Lemma set_app' : forall h1 h2, set (dom h1) -> set (dom h2) -> 
    set (dom (app' h1 h2)).
    induction h1.
    simpl.
    auto.
    simpl.
    intros.
    apply set_add.
    apply IHh1.
    apply (proj2 H).
    auto.
  Qed.

  Definition union h1 h2 := 
    mk_h (app' (lst h1) (lst h2)) (set_app' _ _ (prf h1) (prf h2)).

  Notation "k '+++' m" := (union k m) (at level 69) : heap_scope.

  Lemma app'_nil : forall k, set (dom k) -> app' k nil = k.
    induction k; intros; simpl; auto.
    simpl in H.
    rewrite IHk.
    rewrite add_lst_lb.
    destruct a; auto.
    tauto.
    tauto.
  Qed.

  Lemma add_lst_app': forall lst1 lst2 n w, 
    add_lst n w (app' lst1 lst2) = app' (add_lst n w lst1) lst2.
    induction lst1; simpl; intros; auto.
    destruct a as [a b]; simpl.
    generalize (addr_lt_classic a n); intro X; inversion_clear X. 
    rewrite H.
    simpl.
    rewrite <-IHlst1.
    apply add_lst_add_lst.
    generalize (addr_lt_true _ _ H); intro.
    generalize (mylt_neq _ _ H0); intro.
    auto.
    rewrite H.
    generalize (beq_addr_classic a n); intro X; inversion_clear X. 
    rewrite H0.
    simpl.
    generalize (beq_addr_true _ _ H0); intro; subst a.
    rewrite add_lst_add_lst'.
    auto.
    rewrite H0.
    simpl.
    auto.
  Qed.

  Lemma app'_com : forall l1 l2, set (dom l1) -> set (dom l2) ->
    inter (dom l1) (dom l2) nil ->
    app' l1 l2 = app' l2 l1.
    induction l1; simpl; intros.
    rewrite app'_nil; auto.
    destruct a as [a b].
    simpl in H; simpl in H1; simpl.
    induction l2.
    simpl.
    rewrite app'_nil.
    rewrite add_lst_lb; auto.
    tauto.
    tauto.
    destruct a0 as [a0 b0].
    simpl in H0; simpl in H1; simpl.
    rewrite <-IHl2.
    rewrite <-add_lst_add_lst.
    rewrite IHl1.
    simpl.
    rewrite IHl1.
    auto.
    tauto.
    tauto.
    apply inter_stren with a.
    apply inter_sym.
    apply inter_stren with a0.
    apply inter_sym.
    auto.
    tauto.
    auto.
    simpl.
    apply inter_stren with a.
    auto.
    intro; subst a0.
    generalize (H1 a); intro X; inversion_clear X.
    apply H2; simpl; auto.
    tauto.
    apply inter_sym.
    apply inter_stren with a0.
    apply inter_sym.
    auto.
  Qed.
  
  Lemma update'_app' : forall (l1 l2:list (l*v)) (n:l) (z:v),
    In n (dom l1) /\ ~ In n (dom l2) ->
    app' (update' n z l1) l2 = update' n z (app' l1 l2).
    induction l1.
    simpl.
    tauto.
    destruct a as [a b]; simpl; intros.
    inversion_clear H.
    inversion_clear H0.
    subst n.
    rewrite <-beq_addr_refl.
    simpl.
    rewrite update_add_lst.
    auto.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    generalize (beq_addr_true _ _ H0); intro.
    subst n.
    rewrite <-beq_addr_refl.
    simpl.
    rewrite update_add_lst.
    auto.
    rewrite H0.
    simpl.
    rewrite update_add_lst'.
    rewrite IHl1.
    auto.
    auto.
    generalize (beq_addr_false _ _ H0); intro.
    auto.
  Qed.

  Lemma lookup'_app'_L : forall l1 l2 n z,
    lookup' n l1 = Some z ->
    lookup' n (app' l1 l2) = Some z.
    induction l1; simpl; intros.
    discriminate.
    destruct a as [a b].
    simpl in H; simpl.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    generalize (beq_addr_true _ _ H0); intro.
    subst n.
    rewrite lookup'_add_lst.
    rewrite H0 in H; auto.
    rewrite lookup'_add_lst'.
    apply IHl1; auto.
    rewrite H0 in H; auto.
    apply beq_addr_false.
    rewrite beq_addr_com; auto.
  Qed.

  Lemma lookup'_app'_R : forall l1 l2 n z,
    inter (dom l1) (dom l2) nil ->
    lookup' n l2 = Some z ->
    lookup' n (app' l1 l2) = Some z.
    induction l1.
    simpl.
    auto.
    simpl.
    intros.
    destruct a as [a b].
    simpl in H; simpl.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    generalize (H n); intro X; inversion_clear X.
    simpl in H2.
    generalize (beq_addr_true _ _ H1); intro.
    subst n.
    generalize (lookup'_In _ _ _ H0); intro.
    tauto.
    rewrite lookup'_add_lst'.
    apply IHl1; auto.
    apply inter_stren with a.
    auto.
    apply beq_addr_false.
    rewrite beq_addr_com; auto.
  Qed.

  Lemma In_dom_union : forall k x, In x (dom (lst k)) ->
    forall m, In x (dom (lst (k +++ m))).
    unfold union; simpl.
    destruct k.
    destruct m.
    induction lst0.
    simpl in H.
    contradiction.
    induction a; simpl.
    simpl in s.
    simpl in H.
    inversion_clear H.
    subst a.
    apply In_dom_add_lst.
    simpl in IHlst0.
    apply In_dom_add_lst'.
    apply IHlst0.
    intuition.
    intuition.
  Qed.    

  Lemma equal_union_emp : forall h1, h1 +++ emp = h1.
    intros.
    apply equal_ext.
    destruct h1 as [h1 s1].
    induction h1.
    red; simpl.
    auto.
    induction a.
    red; simpl.
    rewrite app'_nil.
    simpl in s1.
    apply add_lst_lb.
    apply (proj1 s1).
    apply (proj2 s1). 
  Qed.

  Lemma In_dom_union' : forall m k x, In x (dom (lst k)) -> 
    In x (dom (lst (m +++ k))).
    destruct m.
    destruct k.
    generalize lst0 s lst1 s0.
    clear lst0 s lst1 s0.
    unfold union; simpl.
    induction lst0.
    simpl.
    intros.
    auto. 
    induction a; simpl; intros.
    apply In_dom_add_lst'.
    apply IHlst0.
    intuition.
    intuition.
    intuition.
  Qed.

  Lemma union_assoc : forall h1 h2 h3, h1 +++ (h2 +++ h3) = (h1 +++ h2) +++ h3.
    destruct h1; destruct h2; destruct h3.
    apply equal_ext.
    unfold equal; unfold union; simpl.
    induction lst0.
    auto.
    destruct a as [a b].
    simpl.
    rewrite IHlst0.
    rewrite add_lst_app'.
    auto.
    exact (proj2 s).
  Qed.

  Lemma In_union_dom : forall k m x, In x (dom (lst (k +++ m))) ->
    In x (dom (lst k)) \/ In x (dom (lst m)).
    destruct m.
    destruct k.
    generalize lst0 s lst1 s0.
    clear lst0 s lst1 s0.
    unfold union; simpl.
    induction lst1.
    simpl.
    intuition.
    induction a; simpl; intros.
    simpl in H.  
    generalize (add_lst'_In_dom _ _ _ _ H); intro X; inversion_clear X.
    intuition.
    generalize (IHlst1 (proj2 s0) x H0); intro X; inversion_clear X.
    intuition.
    intuition.
  Qed.

  Lemma lookup_union_or: forall h1 h2 n z,
    lookup n (h1 +++ h2) = Some z ->
    lookup n h1 = Some z \/ lookup n h2 = Some z.
    destruct h1.
    destruct h2.
    unfold union; unfold lookup.
    simpl.
    generalize lst0 s lst1 s0.
    clear lst0 s lst1 s0.
    induction lst0.
    simpl.
    auto.
    induction a; simpl; intros.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    rewrite H0.
    rewrite (beq_addr_true _ _ H0) in H.
    rewrite lookup'_add_lst in H.
    left; auto.
    rewrite H0.
    rewrite lookup'_add_lst' in H.
    eapply IHlst0.
    intuition.
    intuition.
    auto.
    generalize (beq_addr_false _ _ H0); auto.
  Qed.

  Lemma lookup_update : forall x y z st, x <> y -> lookup x st = lookup x (singleton y z +++ st).
    destruct st.
    induction lst0.
    unfold lookup; unfold union; unfold singleton; simpl.
    intros.
    rewrite (beq_dif_false_addr x y H).
    auto.
    induction a; unfold lookup; unfold union; unfold singleton; simpl.
    intros.
    generalize (beq_addr_classic x a); intro X; inversion_clear X.
    rewrite H0.
    generalize (addr_lt_classic a y); intro X; inversion_clear X.
    rewrite H1.
    simpl.
    rewrite H0.
    auto.
    rewrite H1.
    generalize (beq_addr_classic a y); intro X; inversion_clear X.
    rewrite <- (beq_addr_true _ _ H2) in H.
    rewrite <- (beq_addr_true _ _ H0) in H.
    tauto.
    rewrite H2.
    simpl.
    rewrite <- (beq_addr_true _ _ H0) in H2.
    rewrite H2.
    rewrite H0.
    auto.
    rewrite H0.
    generalize (beq_addr_classic a y); intro X; inversion_clear X.
    generalize (addr_lt_classic a y); intro X; inversion_clear X.
    rewrite <- (beq_addr_true _ _ H1) in H2.
    rewrite addr_lt_irrefl in H2.
    inversion H2.
    rewrite H2.
    rewrite H1.
    simpl.
    rewrite H0.
    auto.
    rewrite H1.
    generalize (addr_lt_classic a y); intro X; inversion_clear X.
    rewrite H2.
    simpl.
    rewrite H0.
    generalize (IHlst0 (proj2 s) H); intros.
    unfold lookup in H3; unfold union in H3; unfold singleton in H3; simpl in H3.
    auto.
    rewrite H2.
    simpl.
    rewrite (beq_dif_false_addr _ _ H).
    rewrite H0.
    auto.
  Qed.   

  Lemma lookup_update' : forall x z st, lookup x (singleton x z +++ st) = Some z.
    destruct st.
    induction lst0.
    unfold lookup; unfold union; unfold singleton; simpl.
    rewrite <- beq_addr_refl; auto.
    induction a.
    unfold lookup; unfold union; unfold singleton; simpl.
    generalize (addr_lt_classic a x); intro X; inversion_clear X.
    rewrite H.
    simpl.
    generalize (beq_addr_classic x a); intro X; inversion_clear X.
    rewrite <- (beq_addr_true _ _ H0) in H.
    rewrite addr_lt_irrefl in H.
    inversion H.
    rewrite H0.
    generalize (IHlst0 (proj2 s)); intros.
    unfold lookup in H1; unfold union in H1; unfold singleton in H1; simpl in H1.
    auto.
    rewrite H.
    generalize (beq_addr_classic a x); intro X; inversion_clear X.
    rewrite H0.
    simpl.
    rewrite beq_addr_com.
    rewrite H0.
    auto.
    rewrite H0.
    simpl.
    rewrite <- beq_addr_refl; auto.
  Qed.  
  
  (***********
    disjoint
   ***********)

  Definition disjoint h1 h2 := inter (dom (lst h1)) (dom (lst h2)) nil.

  Notation "k '#' m" := (disjoint k m) (at level 79) : heap_scope.

  Lemma disjoint_emp : forall h, h # emp.
    unfold disjoint.
    unfold inter.
    destruct h0.
    simpl.
    intuition.
  Qed.

  Lemma disjoint_singleton : forall x y z z',
    x <> y -> singleton x z # singleton y z'.
    red.
    red.
    firstorder.
    simpl in H1.
    simpl in H0.
    subst x.
    subst y.
    simpl.
    auto.
  Qed.

  Lemma disjoint_singleton' : forall x y z z',
    singleton x z # singleton y z' -> x <> y.
    red.
    intros.
    unfold disjoint in H.
    unfold inter in H.
    subst x.
    unfold singleton in H.
    simpl in H.
    generalize (H y); intro X; inversion_clear X.
    intuition.
  Qed.

  Lemma disjoint_com: forall h1 h2, h1 # h2 -> h2 # h1.
    intros.
    unfold disjoint.
    red; split; intros.
    unfold disjoint in H.
    red in H.
    generalize (H x); intro X; inversion_clear X; tauto.
    red in H0; tauto.
  Qed.

  Lemma disjoint_update : forall n z h1 h2,
    h1 # h2 -> (update n z h1) # h2.
    unfold disjoint.
    intros.
    rewrite (update_dom h1 n z).
    auto.
  Qed.

  Lemma distributivity : forall h1 h2 h0,
    h0 # (h1 +++ h2) <-> h0 # h1 /\ h0 # h2.
    split; intros.
    split.
    red; red; split; intros.
    red in H; red in H.
    generalize (H x); intro X; inversion_clear X.
    apply H1.
    split.
    intuition.
    apply In_dom_union.
    intuition.
    simpl in H0; contradiction.
    red; red; split; intros.
    red in H; red in H.
    generalize (H x); intro X; inversion_clear X.
    apply H1.
    split.
    intuition.
    apply In_dom_union'.
    intuition.
    simpl in H0.
    contradiction.
    inversion_clear H.
    red; red; split; intros.
    inversion_clear H.
    generalize (In_union_dom _ _ _ H3); intro.
    inversion_clear H.
    red in H0.
    red in H0.
    generalize (H0 x); tauto.
    red in H1; red in H1.
    generalize (H1 x); tauto.
    simpl in H; contradiction.
  Qed.

  Lemma disjoint_union : forall h1 h2 h0,
    h0 # h1 /\ h0 # h2 -> h0 # (h1 +++ h2).
    intros.
    generalize (distributivity h1 h2 h0); intro.
    tauto.
  Qed.

  Lemma disjoint_union' : forall h1 h2 h0,  h0 # (h1 +++ h2) -> h0 # h1 /\ h0 # h2.
    intros.
    generalize (distributivity h1 h2 h0); intro.
    intuition.
  Qed.

  Lemma equal_union_disjoint : forall x1 x2 x0, (x1 +++ x2) # x0 -> x1 # x0.
    intros.
    generalize (distributivity x1 x2 x0); intro.
    inversion_clear H0.
    assert (x0 # (x1 +++ x2)).
    apply disjoint_com.
    auto.
    generalize (H1 H0); intro.
    inversion_clear H3.  
    apply disjoint_com.
    auto.
  Qed.

  (* union is commutative only when sets are disjoint *)
  Lemma union_com : forall h1 h2, h1 # h2 -> h1 +++ h2 = h2 +++ h1.
    intros.
    apply equal_ext.
    unfold union; unfold equal; simpl.
    induction h1.
    induction h2.
    simpl.
    unfold disjoint in H; unfold inter in H; simpl in H.
    apply app'_com; auto.
  Qed.
    
  Lemma lookup_union : forall h1 h2, h1 # h2 ->
    forall n z, lookup n h1 = Some z -> 
      lookup n (h1 +++ h2) = Some z.
    destruct h1; destruct h2.
    unfold disjoint; unfold inter; unfold union; unfold lookup; simpl.
    intros.
    apply lookup'_app'_L; auto.
 Qed.
    
  Lemma lookup_union_R : forall h1 h2, h1 # h2 ->
    forall n z, lookup n h2 = Some z -> 
      lookup n (h1 +++ h2) = Some z.
    destruct h1; destruct h2.
    unfold disjoint; unfold inter; unfold union; unfold lookup; simpl.
    intros.
    apply lookup'_app'_R; auto.
  Qed.

  Lemma equal_update_L : forall (h1 h2:h), h1 # h2 ->
    forall (n:l) (z z1:v), lookup n h1 = Some z1 ->
      update n z (h1 +++ h2) = (update n z h1) +++ h2.
    intros.
    apply equal_ext.
    destruct h1; destruct h2.
    unfold disjoint; unfold inter; unfold equal; unfold union.
    simpl.
    rewrite update'_app'; auto.
    generalize (H n); intro.
    simpl in H1.
    generalize (lookup'_In _ _ _ H0); intro.
    simpl in H2.
    tauto.
  Qed.
  
  Lemma equal_update_R : forall (h1 h2:h), h1 # h2 ->
    forall (n:l) (z z2:v), lookup n h2 = Some z2 ->
      update n z (h1 +++ h2) = h1 +++ (update n z h2).
    intros.
    apply equal_ext.
    destruct h1; destruct h2.
    unfold disjoint; unfold inter; unfold equal; unfold union.
    simpl.
    rewrite (app'_com lst0 (update' n z lst1)); auto.
    rewrite update'_app'; auto.
    rewrite app'_com; auto.
    unfold lookup in H0.
    simpl in H0.
    generalize (lookup'_In _ _ _ H0); intro.
    split; auto.
    generalize (H n); intro X; inversion_clear X.
    intro.
    simpl in H3.
    tauto.
    apply set_update; auto.
    generalize (update_dom (mk_h lst1 s0) n z); intro.
    unfold update in H1; simpl in H1.
    rewrite H1; auto.
  Qed.

  Lemma lookup_exists_partition : forall h a b,
    lookup a h = Some b ->
    exists h'' ,     
      h = (singleton a b) +++ h'' /\ (singleton a b) # h''.
    destruct h0.
    unfold union; unfold lookup; unfold disjoint; unfold inter.
    simpl.
    generalize lst0 s; clear lst0 s.
    induction lst0.
    simpl.
    intros.
    discriminate.
    induction a; simpl.
    intros until a0.
    generalize (beq_addr_classic a0 a); intro X; inversion_clear X.
    rewrite H.
    generalize (beq_addr_true _ _ H); clear H; intro; subst a0.
    intros; injection H; clear H; intro; subst b0.
    exists (mk_h lst0 (proj2 s)).
    simpl.
    split.
    apply equal_ext.
    unfold equal.
    simpl.
    rewrite add_lst_lb.
    auto.
    intuition.
    intros.
    intuition.
    subst a.
    generalize (lb_notin' _ _ H3); intro.
    tauto.
    rewrite H.
    intros.
    generalize (IHlst0 (proj2 s) a0 b0 H0); intros.
    inversion_clear H1.
    inversion_clear H2.
    generalize (equal_ext' _ _ H1); clear H1; intro H1.
    unfold equal in H1.
    simpl in H1.
    destruct x.
    exists (singleton a b  +++ (mk_h lst1 s0)).
    simpl.
    subst lst0.
    split.
    apply equal_ext.
    unfold equal; simpl.
    inversion_clear s.
    rewrite add_lst_add_lst.
    rewrite <- add_lst_lb.
    auto.
    auto.
    generalize (beq_addr_false _ _ H); auto.
    intros.
    generalize (H3 x).
    intros.
    intuition.
    subst a0.
    apply H8.
    eapply In_dom_add_lst2 with (n:=a).
    generalize (beq_addr_false _ _ H); intro; auto.
    apply H9.
  Qed.

  (*****************
    element removal
   *****************)

  Fixpoint del' (n:l) (k:list (l*v)) {struct k} : list (l*v) :=
    match k with
      nil => nil
      | hd::tl => match beq_addr n (fst hd) with 
                    true => del' n tl
                    | false => hd :: del' n tl
                  end
    end.

  Lemma lb_del' : forall k n, lb n (dom k) -> 
    forall m, lb n (dom (del' m k)).
    induction k; simpl; intros; auto.
    induction a.
    simpl in H.
    inversion_clear H.
    generalize (beq_addr_classic m a); intro X; inversion_clear X.
    generalize (beq_addr_true m a H); intros.
    subst a.
    rewrite <- beq_addr_refl.
    intuition.
    simpl.
    rewrite H.
    simpl.
    split; auto.
  Qed.

  Lemma lb_del'' : forall k n, lb n (dom k) -> del' n k = k.
    induction k; simpl; intros; auto.
    induction a.
    simpl in H.
    inversion_clear H.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    simpl.
    rewrite H.
    generalize (beq_addr_true n a H); intros.
    subst a.
    generalize (otf.lt_antirefl H0); tauto.
    simpl.
    rewrite H.
    rewrite IHk; auto.
  Qed.

  Lemma set_del' : forall k, set (dom k) -> forall n, set (dom (del' n k)).
    induction k.
    simpl.
    auto.
    induction a; simpl; intros.
    inversion_clear H.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    generalize (beq_addr_true n a H); intros.
    subst a.
    rewrite <- beq_addr_refl.
    intuition.
    rewrite H.
    simpl.
    split.
    apply lb_del'.
    auto.
    auto.
  Qed.

  Definition dif h l := mk_h (del' l (lst h) ) (set_del' (lst h) (prf h) l).

  Notation "k '---' m" := (dif k m) (at level 69) : heap_scope.
  
  Lemma dif_singleton_emp: forall a b, (singleton a b) --- a = emp.
    intros.
    apply equal_ext.
    unfold singleton.
    unfold dif.
    simpl.
    unfold equal.
    simpl.
    rewrite <- beq_addr_refl.
    reflexivity.
  Qed.

  Lemma add_lst_del': forall lst n w n', set (dom lst) -> 
    n' <> n -> add_lst n w (del' n' lst) = del' n' (add_lst n w lst).
    induction lst0.
    simpl; intros.
    rewrite (beq_dif_false_addr n' n H0); simpl.
    auto.
    induction a; simpl; intros.
    inversion_clear H.
    generalize (beq_dif_false_addr n' n H0); intros.
    generalize (beq_addr_classic n' a); intro X; inversion_clear X. 
    rewrite H3.
    generalize (addr_lt_classic a n); intro X; inversion_clear X. 
    rewrite H4.
    generalize (beq_addr_true n' a H3); intro; subst n'; simpl; rewrite <- beq_addr_refl; intuition.
    rewrite H4.
    generalize (beq_addr_classic a n); intro X; inversion_clear X. 
    generalize (beq_addr_true n' a H3); intros.
    generalize (beq_addr_true a n H5); intros.
    subst n'.
    subst n.
    generalize (beq_addr_true _ _ H5); intro.
    tauto.
    rewrite H5.
    simpl.
    rewrite H.
    rewrite H3.
    rewrite IHlst0.
    generalize (beq_addr_true n' a H3); intros.
    subst a.
    clear H H5 H3.
    rewrite add_lst_lb.
    simpl.
    rewrite (beq_dif_false_addr n' n H0).
    auto.
    eapply lb_trans.
    red.
    apply H1.
    generalize (addr_lt_classic n n'); intro X; inversion_clear X. 
    apply addr_lt_true.
    auto.
    generalize (addr_lt_false n' n H4); intros.
    generalize (addr_lt_false n n' H); intros.
    assert (n = n').
    apply myle_ge_eq; auto.
    subst n.
    tauto.
    auto.
    auto.
    rewrite H3.
    simpl.
    generalize (addr_lt_classic a n); intro X; inversion_clear X. 
    rewrite H4.
    simpl.
    rewrite H3.
    rewrite IHlst0.
    auto.
    auto.
    auto.
    rewrite H4.
    generalize (beq_addr_classic a n); intro X; inversion_clear X. 
    rewrite H5.
    simpl.
    rewrite H3.
    auto.
    rewrite H5.
    simpl.
    rewrite H.
    rewrite H3.
    auto.
  Qed.

  Lemma add_lst_del'': forall lst n w, del' n (add_lst n w lst) = del' n lst.
    induction lst0.
    simpl.
    intros.
    rewrite <- beq_addr_refl.
    auto.
    induction a; simpl; auto.
    intros.
    generalize (addr_lt_classic a n); intro X; inversion_clear X. 
    rewrite H.
    generalize (beq_addr_classic n a); intro X; inversion_clear X. 
    generalize (beq_addr_true n a H0); intros.
    generalize (addr_lt_true a n H); intros.
    subst a.
    generalize (otf.lt_antirefl H2); tauto.
    rewrite H0.
    simpl.
    rewrite H0.
    rewrite IHlst0.
    auto.
    rewrite H.
    generalize (beq_addr_classic a n); intro X; inversion_clear X. 
    rewrite H0.
    rewrite beq_addr_com.
    rewrite H0.
    simpl.
    rewrite beq_addr_com.
    rewrite H0.
    auto.
    rewrite H0.
    rewrite beq_addr_com.
    rewrite H0.
    simpl.
    rewrite <- beq_addr_refl.
    rewrite beq_addr_com.
    rewrite H0.
    auto.
  Qed.

  Lemma lookup'_del' : forall w st, lookup' w (del' w st) = None.
    induction st.
    auto.
    simpl.
    induction a.
    simpl.
    generalize (beq_addr_classic w a); intro X; inversion_clear X.
    rewrite H.
    auto.
    rewrite H.
    simpl.
    rewrite H.
    auto.
  Qed.
  
  Lemma lookup'_del'' : forall st x y, x <> y -> 
    lookup' x (del' y st) = lookup' x st.
    induction st; auto.
    induction a; simpl; intros.
    generalize (beq_addr_classic y a); intro X; inversion_clear X.
    rewrite H0.
    generalize (beq_addr_classic x a); intro X; inversion_clear X.
    assert (x=y).
    generalize (beq_addr_true _ _ H0); intro.
    generalize (beq_addr_true _ _ H1); intro.
    subst a; auto.
    contradiction.
    rewrite H1.
    auto.
    rewrite H0.
    simpl.
    generalize (beq_addr_classic x a); intro X; inversion_clear X.
    rewrite H1.
    auto.
    rewrite H1.
    auto.
  Qed.

  Lemma del'_app' : forall k m n, set (dom m) -> set (dom k) -> 
    del' n (app' k m) = app' (del' n k) (del' n m).
    induction k; simpl; auto.
    induction a.
    simpl.
    intros.
    generalize (beq_addr_classic n a); intro X; inversion_clear X.
    rewrite H1.
    rewrite (beq_addr_true  n a H1).
    rewrite add_lst_del''.
    intuition.
    rewrite H1.
    simpl.
    rewrite <- add_lst_del'.
    rewrite IHk.
    auto.
    intuition.
    intuition.
    apply set_app'.
    intuition.
    intuition.
    apply beq_addr_false; auto.
  Qed.

  Lemma dif_not_in_dom: forall h l,
    ~(In l (dom (lst h))) ->
    (h --- l) = h.
    intros.
    apply equal_ext.
    destruct h0 as [h0 s0].
    induction h0.
    intros.
    unfold dif; unfold equal.
    simpl.
    auto.
    intros.
    unfold dif; unfold equal.
    induction a.
    simpl.
    generalize (beq_addr_classic l0 a); intro X; inversion_clear X.
    rewrite (beq_addr_true _ _ H0) in H.
    simpl in H.
    intuition.
    rewrite H0; simpl.  
    unfold dif in IHh0; unfold equal in IHh0; simpl  in IHh0.
    assert (~(In l0 (dom (lst (mk_h h0 (proj2 s0)))))).
    simpl in H.
    simpl; red; intros.
    intuition.
    rewrite (IHh0 (proj2 s0) H1).
    auto.
  Qed.

  Lemma dif_union: forall h1 h2 a,
    (h1 +++ h2) --- a = (h1 --- a) +++ (h2 --- a).
    intros.
    apply equal_ext.
    destruct h1 as [h1 s1].
    destruct h2 as [h2 s2].
    unfold dif.
    unfold union.
    simpl.
    apply (del'_app' h1 h2 a s2 s1).
  Qed.

  Lemma dif_disjoint: forall h a b, h # (singleton a b) -> h --- a = h.
    destruct h0 as [h0 s0].
    intros.
    apply dif_not_in_dom.
    red; intros.
    simpl in H0.
    unfold disjoint in H.
    unfold inter in H.
    unfold singleton in H.
    simpl in H.
    generalize (H a); intros.
    tauto.
  Qed.

  Lemma In_dom_del' : forall k x y, x <> y ->
    In x (dom (del' y k)) ->
    In x (dom k).
    induction k.
    simpl.
    auto.
    induction a; simpl; intros.
    generalize (beq_addr_classic y a); intro X; inversion_clear X.
    generalize (beq_addr_true _ _ H1); intro; subst y.
    rewrite <- beq_addr_refl in H0.
    right; eapply IHk.
    apply H.
    auto.
    rewrite H1 in H0.
    simpl in H0.
    inversion_clear H0.
    intuition.
    right; eapply IHk.
    apply H.
    auto.
  Qed.

  Lemma dif_disjoint': forall h1 h2 l, h1 # h2 -> h1 --- l # h2 --- l.
    destruct h1 as [h1 s1].
    destruct h2 as [h2 s2].
    unfold disjoint; unfold inter; unfold dif.
    simpl.
    generalize h1 s1 h2 s2.
    clear h1 s1 h2 s2.
    induction h1.
    simpl.
    intuition.
    induction a; simpl.
    intros.
    generalize (beq_addr_classic l0 a); intro X; inversion_clear X.
    generalize (beq_addr_true _ _ H0); intro; subst l0.
    rewrite <- beq_addr_refl.
    apply IHh1.
    intuition.
    intuition.
    intros.
    generalize (H x0); intros.
    intuition.
    rewrite H0.
    simpl.
    generalize (beq_addr_false _ _ H0); intros.
    assert (forall x, In x (dom h1) /\ In x (dom h2) <-> False) .
    intros.
    generalize (H x0); intro.
    intuition.
    generalize (IHh1 (proj2 s1) _ s2 l0 H2); intro.
    generalize (H3 x).
    generalize (H x).
    intros; intuition.
    subst a.
    apply H13.
    eapply In_dom_del'.
    assert (x <> l0).
    auto.
    apply H4.
    auto.
  Qed.

  Lemma compose_union_equiv: forall h a b (s: set (dom ((a,b)::h))) 
    (s': set (dom h)) , 
    mk_h ((a,b) :: h) s === (singleton a b) +++ (mk_h h s').
    unfold union.
    unfold equal.
    simpl.
    induction h0.
    simpl; auto.
    induction a; simpl; intros.
    generalize (addr_lt_classic a a0); intro X; inversion_clear X.
    decompose [and] s.
    generalize (addr_lt_true _ _ H); intro.
    assert (~ (a < a0)).
    apply otf.lt_not_gt.
    auto.
    tauto.
    rewrite H.
    generalize (beq_addr_classic a a0); intro X; inversion_clear X.
    decompose [and] s.
    generalize (beq_addr_true _ _ H0); intro.
    subst a.
    generalize (otf.lt_antirefl H3); tauto.
    rewrite H0.
    auto.
  Qed.

  Lemma lookup_disjoint_None: forall h a b,
    h # singleton a b -> lookup a h = None.
    destruct h0.
    induction lst0.
    simpl; auto.
    unfold lookup; unfold disjoint; unfold inter.
    induction a; simpl; intros.
    simpl in s.
    generalize (beq_addr_classic a0 a); intro X; inversion_clear X.
    generalize (beq_addr_true a0 a H0); intro; subst a0.
    generalize (H a); intro; intuition.
    rewrite H0.
    unfold lookup in IHlst0.
    simpl in IHlst0.
    apply (IHlst0 (proj2 s) a0 b).
    unfold disjoint; unfold inter.
    simpl.
    intros.
    generalize (H x); intros.
    tauto.
  Qed.

  Lemma disjoint_comp : forall h'1 h1 h2 h'2,
    h1 # h'1 ->
    h1 # h2 ->
    h'1 # h'2 ->
    h'1 +++ h'2 = h1 +++ h2 ->
    exists h', h'1 # h' /\ h2 = (h' +++ h'1).
    destruct h'1.
    generalize lst0 s; clear lst0 s.
    induction lst0.
    simpl; intros.
    exists h2.
    assert (mk_h nil s = emp).
    unfold emp.
    rewrite (proof_irrelevance _ s set_nil).
    auto.
    rewrite H3.
    clear H3.
    split.
    apply disjoint_com.
    apply disjoint_emp.
    apply sym_eq.
    apply equal_union_emp.
    induction a; simpl; intros.
    assert (a_set: set (dom ((a,b)::nil))).
    red.
    simpl.
    tauto.
    assert (lookup a (mk_h ((a, b) :: lst0) s +++ h'2) = Some b).
    unfold lookup.
    simpl.
    rewrite lookup'_add_lst.
    auto.
    assert (lookup a (h1 +++ h2) = Some b).
    rewrite <- H2.
    auto.
    assert (lst0_set: set (dom lst0)).
    simpl in s.
    inversion_clear s; auto.
    assert (lookup a  h2 = Some b).
    generalize (lookup_union_or h1 h2 a b H4); intro X; inversion_clear X.
    assert (h1 # (singleton a b) +++ mk_h lst0 lst0_set).
    assert ( mk_h ((a, b) :: lst0) s = singleton a b +++ mk_h lst0 lst0_set ).
    apply equal_ext.
    apply (compose_union_equiv lst0 a b s lst0_set).
    rewrite <-H6.
    auto.
    generalize (disjoint_union' _ _ _ H6); intro X; inversion_clear X.
    generalize (lookup_disjoint_None h1 a b H7); intro.
    rewrite H5 in H9; inversion H9.
    auto.
    generalize (lookup_exists_partition _ _ _ H5); intro.
    inversion_clear H6.
    decompose [and] H7; clear H7.

    assert (L1: h1 # mk_h lst0 lst0_set).
    unfold disjoint; unfold inter.
    intros.
    unfold disjoint in H; unfold inter in H.
    generalize (H x0); intro.
    simpl in H7.
    simpl.
    intuition.

    assert (L2: h1 # x).
    apply disjoint_com.
    apply equal_union_disjoint with (singleton a b).
    assert (h2 = x +++ singleton a b).
    apply trans_eq with (singleton a b +++ x).
    auto.
    apply union_com.
    auto.
    rewrite <-H7.
    apply disjoint_com; auto.

    assert (L3: mk_h lst0 lst0_set # h'2).
    unfold disjoint; unfold inter; simpl.
    intros.
    generalize (H1 x0).
    intros.
    unfold disjoint in H7; unfold inter in H7; simpl in H7.
    intuition.

    assert (L4: mk_h lst0 lst0_set +++ h'2 = h1 +++ x).
    assert (mk_h ((a, b) :: lst0) s +++ h'2 = h1 +++ singleton a b +++ x).
    apply trans_eq with (h1 +++ h2).
    auto.
    apply trans_eq with (h1 +++ (singleton a b +++ x)).
    apply trans_eq with (h2 +++ h1).
    apply union_com.
    auto.
    apply trans_eq with ((singleton a b +++ x) +++ h1).
    rewrite <-H6.
    auto.
    apply union_com.
    apply disjoint_com.
    rewrite <-H6; auto.
    apply union_assoc.
    assert (mk_h ((a, b) :: lst0) s +++ h'2 = singleton a b +++ h1 +++  x).
    apply trans_eq with (h1 +++ singleton a b +++ x).
    auto.
    assert ( h1 +++ singleton a b = singleton a b +++ h1 ).
    apply union_com.
    apply disjoint_com.
    apply equal_union_disjoint with x.
    rewrite <-H6.
    apply disjoint_com.
    auto.
    rewrite H9.
    auto.
    destruct x; destruct h1; destruct h'2.
    unfold union in H9; unfold equal in H9.
    simpl in H9.
    assert ( (mk_h ((a, b) :: lst0) s +++ mk_h lst3 s2) --- a =
      ((mk_h lst2 s1 +++ singleton a b) +++ mk_h lst1 s0) --- a ).		
    rewrite H7.
    auto.
    generalize (dif_union (mk_h ((a, b) :: lst0) s) (mk_h lst3 s2) a); intros.
    generalize (dif_union (mk_h lst2 s1 +++ singleton a b) (mk_h lst1 s0) a); intros.
    generalize (dif_union (mk_h lst2 s1) (singleton a b) a); intros.

    assert (A1: mk_h lst2 s1 --- a = mk_h lst2 s1).
    apply dif_disjoint with b.
    unfold disjoint in H.
    unfold inter in H.
    unfold disjoint.
    unfold inter.
    intros.
    generalize (H x); intros.
    simpl; simpl in H14.
    tauto.

    rewrite (dif_singleton_emp a b) in H13.
    rewrite A1 in H13; clear A1.
    rewrite (equal_union_emp (mk_h lst2 s1)) in H13.
    rewrite H13 in H12.
    clear H13.

    assert (A1: mk_h lst1 s0 --- a = mk_h lst1 s0).
    apply dif_disjoint with b.
    apply disjoint_com; auto.

    rewrite A1 in H12; clear A1.
    rewrite H12 in H10.
    clear H12.

    assert (A1: mk_h lst3 s2 --- a = mk_h lst3 s2).
    apply dif_disjoint with b.
    unfold disjoint in H1.
    unfold inter in H1.
    unfold disjoint.
    unfold inter.
    intros.
    generalize (H1 x); intros.
    simpl; simpl in H12.
    tauto.

    rewrite A1 in H11; clear A1.
    assert (A1: (mk_h ((a, b) :: lst0) s --- a) = mk_h lst0 lst0_set).
    apply equal_ext.
    unfold equal; unfold dif; simpl.
    rewrite <- beq_addr_refl.
    apply lb_del''.
    apply (proj1 s).

    rewrite A1 in H11; clear A1.
    rewrite H11 in H10; clear H11.
    auto.

    generalize (IHlst0 lst0_set h1 x h'2 L1 L2 L3 L4).
    intros.
    inversion_clear H7.
    inversion_clear H9.
    exists x0.

    split.

    apply disjoint_com.
    assert ( mk_h ((a, b) :: lst0) s = singleton a b +++ (mk_h lst0 lst0_set) ).
    apply equal_ext.
    apply compose_union_equiv.
    rewrite H9.
    apply disjoint_union.
    split.
    apply equal_union_disjoint with (mk_h lst0 lst0_set).
    rewrite <-H10.
    apply disjoint_com; auto.
    apply disjoint_com; auto.
    apply sym_eq.

    apply trans_eq with (x0 +++ (singleton a b +++ mk_h lst0 lst0_set)).

    assert ( mk_h ((a, b) :: lst0) s = singleton a b +++ mk_h lst0 lst0_set).
    apply equal_ext.
    apply compose_union_equiv.
    rewrite H9.
    auto.

    apply trans_eq with (((singleton a b) +++ (mk_h lst0 lst0_set)) +++ x0).
    apply union_com.
    apply disjoint_union.
    split.
    apply equal_union_disjoint with (mk_h lst0 lst0_set).
    rewrite <- H10.
    apply disjoint_com; auto.
    apply disjoint_com; auto.
    apply trans_eq with (singleton a b +++ (mk_h lst0 lst0_set +++ x0) ).
    apply sym_eq.
    apply union_assoc.
    assert ( (mk_h lst0 lst0_set) +++ x0 = x0 +++ (mk_h lst0 lst0_set) ).
    apply union_com.
    auto.
    rewrite H9.
    rewrite <- H10.
    auto.
  Qed.

  Lemma lookup_dif : forall w st, lookup w (st --- w) = None.
    intros.
    unfold lookup.
    unfold dif.
    simpl.
    apply lookup'_del'.
  Qed.
  
  Lemma lookup_dif' : forall st x y, x <> y -> 
    lookup x (st --- y) = lookup x st.
    intros.
    unfold lookup.
    unfold dif.
    simpl.
    apply lookup'_del''.
    auto.
  Qed.

End map.

Module Loc <: OrderedTypeExt.
  Definition t := nat.

  Definition eq := @eq nat.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Definition lt := lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. unfold lt in |- *; intros; apply lt_trans with y; auto. Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. unfold lt, eq in |- *; intros; omega. Qed.

  Definition compare : forall x y : t, OrderedType.Compare lt eq x y.
  Proof.
    intros; case (lt_eq_lt_dec x y).
    simple destruct 1; intro.
    constructor 1; auto.
    constructor 2; auto.
    intro; constructor 3; auto.
  Defined.

  Lemma eq_ext : forall x y : t, eq x y -> x = y.
    intros.
    red in H.
    auto.
  Qed.

End Loc.

Module integer.
  Definition elem := Z.
End integer.

Module heap := map Loc integer.

(* definition of locations and values *)
Definition loc := Loc.t.
Definition val := Z.

(* cast *)
Definition val2loc (z:Z) : loc :=
  match z with
    Z0 => O
    | Zpos p => nat_of_P p
    | Zneg p => nat_of_P p
  end.

Definition loc2val (p:loc) : val := Z_of_nat p.

Lemma Z_of_nat2loc : forall n, val2loc (loc2val n) = n.
  destruct n; auto.
  simpl.
  apply nat_of_P_o_P_of_succ_nat_eq_succ.
Qed.

Notation "k '---' l" := (heap.dif k l) (at level 69) : heap_scope.
Notation "k '+++' m" := (heap.union k m) (at level 69) : heap_scope.
Notation "k '#' m" := (heap.disjoint k m) (at level 79) : heap_scope.
    







