(** Coq development accompanying the paper
      "Formal verification of a C-like memory model
       and its uses for verifying program transformations"
    by Xavier Leroy and Sandrine Blazy. *)

(*  Copyright 2007 Institut National de Recherche en Informatique et
    en Automatique.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>. *)

Require Import List.
Require Import ZArith.
Require Import Znumtheory.
Open Scope Z_scope.

Ltac inv H := inversion H; clear H; subst.

Definition zeq: forall (z1 z2: Z), {z1=z2} + {z1<>z2}  := Z_eq_dec.
Definition zle: forall (z1 z2: Z), {z1<=z2} + {z1>z2}  := Z_le_gt_dec.
Definition zlt: forall (z1 z2: Z), {z1<z2} + {z1>=z2}  := Z_lt_ge_dec.

(** * Section 2: Values and types *)

Parameter val: Set.
Parameter vundef : val.

Parameter memtype: Set.

Parameter compat: memtype -> memtype -> Prop.
Parameter sizeof: memtype -> Z.
Parameter alignof: memtype -> Z.
Parameter convert: memtype -> val -> val.

Axiom compat_dec: forall ty1 ty2, {compat ty1 ty2} + {~compat ty1 ty2}.

Axiom sizeof_pos: forall ty, sizeof ty > 0.

Axiom compat_sizeof:
  forall ty ty', compat ty ty' -> sizeof ty' = sizeof ty.

Axiom alignof_pos: forall ty, alignof ty > 0.

Parameter max_alignment: Z.

Axiom alignof_div: forall ty, (alignof ty | max_alignment).

Locate "|".
Axiom compat_alignof:
  forall ty ty', compat ty ty' -> alignof ty' = alignof ty.

(** * Section 3: Abstract memory model *)

Module Type GEN_MEM.

Variable block: Set.
Hypothesis eq_block: forall (b1 b2: block), {b1=b2} + {b1<>b2}.

Variable mem: Set.

Variable empty: mem.
Variable alloc: mem -> Z -> Z -> option (block * mem).
Variable load: memtype -> mem -> block -> Z -> option val.
Variable store: memtype -> mem -> block -> Z -> val -> option mem.
Variable free: mem -> block -> option mem.

Hypothesis load_alloc_other:
  forall m lo hi b m' ty b' ofs,
  alloc m lo hi = Some (b, m') ->
  b' <> b ->
  load ty m' b' ofs = load ty m b' ofs.

Hypothesis load_store_same:
  forall ty m b ofs v m' ty',
  store ty m b ofs v = Some m' ->
  compat ty ty' ->
  load ty' m' b ofs = Some (convert ty' v).

Hypothesis load_store_disjoint:
  forall ty m b ofs v m' ty' b' ofs',
  store ty m b ofs v = Some m' ->
  b' <> b \/ ofs' + sizeof ty' <= ofs \/ ofs + sizeof ty <= ofs' ->
  load ty' m' b' ofs' = load ty' m b' ofs'.
  
Hypothesis load_free_other:
  forall m b m' ty b' ofs,
  free m b = Some m' ->
  b' <> b ->
  load ty m' b' ofs = load ty m b' ofs.

Variable valid_block: mem -> block -> Prop.

Hypothesis alloc_valid_block:
  forall m lo hi b m' b',
  alloc m lo hi = Some(b, m') ->
  (valid_block m' b' <-> b' = b \/ valid_block m b').

Hypothesis alloc_not_valid_block:
  forall m lo hi b m',
  alloc m lo hi = Some(b, m') -> ~(valid_block m b).

Hypothesis load_valid_block:
  forall ty m b ofs v,
  load ty m b ofs = Some v -> valid_block m b.

Hypothesis store_valid_block:
  forall ty m b ofs v m',
  store ty m b ofs v = Some m' -> valid_block m b.

Hypothesis store_valid_block_inv:
  forall ty m b ofs v m' b',
  store ty m b ofs v = Some m' -> (valid_block m' b' <-> valid_block m b').

Hypothesis free_valid_block:
  forall m b m' b',
  free m b = Some m' -> b' <> b -> (valid_block m' b' <-> valid_block m b').

Hypothesis valid_block_free:
  forall m b,
  valid_block m b -> exists m', free m b = Some m'.

Variable bounds: mem -> block -> Z*Z.

Hypothesis alloc_result_bounds:
  forall m lo hi b m',
  alloc m lo hi = Some(b, m') -> bounds m' b = (lo, hi).

Hypothesis alloc_bounds_inv:
  forall m lo hi b m' b',
  alloc m lo hi = Some(b, m') -> b' <> b -> bounds m' b' = bounds m b'.

Hypothesis store_bounds_inv:
  forall ty m b ofs v m' b',
  store ty m b ofs v = Some m' -> bounds m' b' = bounds m b'.

Hypothesis free_bounds_inv:
  forall m b m' b',
  free m b = Some m' -> b' <> b -> bounds m' b' = bounds m b'.

Definition valid_pointer (ty: memtype) (m: mem) (b: block) (ofs: Z) : Prop :=
  valid_block m b
  /\ (alignof ty | ofs)
  /\ fst (bounds m b) <= ofs
  /\ ofs + sizeof ty <= snd (bounds m b).

Hypothesis valid_pointer_store:
  forall ty m b ofs v,
  valid_pointer ty m b ofs ->
  exists m', store ty m b ofs v = Some m'.

End GEN_MEM.

(** Derived properties of the abstract memory model. *)

Module Gen_Mem_Facts(M: GEN_MEM).

Import M.

Lemma alloc_valid_block_inv:
  forall m lo hi b m' b',
  alloc m lo hi = Some(b, m') -> valid_block m b' -> valid_block m' b'.
Proof.
  intros. rewrite (alloc_valid_block _ _ _ _ _ b' H). auto.
Qed.

Lemma alloc_not_valid_block_2:
  forall m lo hi b m' b',
  alloc m lo hi = Some(b, m') -> valid_block m b' -> b' <> b.
Proof.
  intros. red; intros; subst b'. 
  elim (alloc_not_valid_block _ _ _ _ _ H). auto.
Qed.

Lemma load_alloc_other_2:
  forall m lo hi b m' b' ty ofs v,
  alloc m lo hi = Some(b, m') -> 
  load ty m b' ofs = Some v ->
  load ty m' b' ofs = Some v.
Proof.
  intros. rewrite <- H0. eapply load_alloc_other; eauto.
  red; intro. subst b'. 
  elim (alloc_not_valid_block _ _ _ _ _ H). 
  eapply load_valid_block; eauto.
Qed.

Lemma alloc_result_valid_pointer:
  forall m lo hi b m' ty ofs,
  alloc m lo hi = Some(b, m') ->
  (alignof ty | ofs) -> lo <= ofs -> ofs + sizeof ty <= hi ->
  valid_pointer ty m' b ofs.
Proof.
  intros; red. 
  split. rewrite (alloc_valid_block _ _ _ _ _ b H). tauto. 
  split. auto.
  rewrite (alloc_result_bounds _ _ _ _ _ H). simpl. tauto.
Qed. 

Lemma alloc_valid_pointer_inv:
  forall m lo hi b m' ty b' ofs,
  alloc m lo hi = Some(b, m') ->
  valid_pointer ty m b' ofs -> valid_pointer ty m' b' ofs.
Proof.
  intros. destruct H0 as [A [B [C D]]]. 
  assert (b' <> b). eapply alloc_not_valid_block_2; eauto. 
  split. rewrite (alloc_valid_block _ _ _ _ _ b' H). auto.
  split. auto. 
  rewrite (alloc_bounds_inv _ _ _ _ _ _ H H0). tauto.
Qed.

Lemma store_valid_pointer_inv:
  forall ty m b ofs v m' ty' b' ofs',
  store ty m b ofs v = Some m' ->
  (valid_pointer ty' m' b' ofs' <-> valid_pointer ty' m b' ofs').
Proof.
  intros. unfold valid_pointer. 
  rewrite (store_bounds_inv _ _ _ _ _ _ b' H).
  rewrite (store_valid_block_inv _ _ _ _ _ _ b' H). 
  tauto.
Qed. 

Lemma free_valid_pointer_inv:
  forall m b m' ty b' ofs,
  free m b = Some m' -> b' <> b ->
  (valid_pointer ty m' b' ofs <-> valid_pointer ty m b' ofs).
Proof.
  intros. unfold valid_pointer.
  rewrite (free_bounds_inv _ _ _ _ H H0).
  rewrite (free_valid_block _ _ _ _ H H0).
  tauto.
Qed.

Section LOADV.

Variable proj_pointer: val -> option (block * Z).

Definition loadv (ty: memtype) (m: mem) (v: val) : option val :=
  match proj_pointer v with
  | Some(b, ofs) => load ty m b ofs
  | None => None
  end.

Definition storev (ty: memtype) (m: mem) (addr v: val) : option mem :=
  match proj_pointer addr with
  | Some(b, ofs) => store ty m b ofs v
  | None => None
  end.

End LOADV.

End Gen_Mem_Facts.

(** * Section 4: concrete memory model *)

(** The concrete memory model is first specified by the properties it
  satisfies. *)

Module  Type REF_GEN_MEM.

Variable block: Set.
Hypothesis eq_block: forall (b1 b2: block), {b1=b2} + {b1<>b2}.

Variable mem: Set.

Variable empty: mem.
Variable alloc: mem -> Z -> Z -> option (block * mem).
Variable load: memtype -> mem -> block -> Z -> option val.
Variable store: memtype -> mem -> block -> Z -> val -> option mem.
Variable free: mem -> block -> option mem.

(** Properties inherited from the abstract memory model. *)

Hypothesis load_alloc_other:
  forall m lo hi b m' ty b' ofs,
  alloc m lo hi = Some (b, m') ->
  b' <> b ->
  load ty m' b' ofs = load ty m b' ofs.

Hypothesis load_store_same:
  forall ty m b ofs v m' ty',
  store ty m b ofs v = Some m' ->
  compat ty ty' ->
  load ty' m' b ofs = Some (convert ty' v).

Hypothesis load_store_disjoint:
  forall ty m b ofs v m' ty' b' ofs',
  store ty m b ofs v = Some m' ->
  b' <> b \/ ofs' + sizeof ty' <= ofs \/ ofs + sizeof ty <= ofs' ->
  load ty' m' b' ofs' = load ty' m b' ofs'.
  
Hypothesis load_free_other:
  forall m b m' ty b' ofs,
  free m b = Some m' ->
  b' <> b ->
  load ty m' b' ofs = load ty m b' ofs.

Variable valid_block: mem -> block -> Prop.

Hypothesis alloc_valid_block:
  forall m lo hi b m' b',
  alloc m lo hi = Some(b, m') ->
  (valid_block m' b' <-> b' = b \/ valid_block m b').
Hypothesis alloc_not_valid_block:
  forall m lo hi b m',
  alloc m lo hi = Some(b, m') -> ~(valid_block m b).
Hypothesis load_valid_block:
  forall ty m b ofs v,
  load ty m b ofs = Some v -> valid_block m b.
Hypothesis store_valid_block:
  forall ty m b ofs v m',
  store ty m b ofs v = Some m' -> valid_block m b.
Hypothesis store_valid_block_inv:
  forall ty m b ofs v m' b',
  store ty m b ofs v = Some m' -> (valid_block m' b' <-> valid_block m b').
Hypothesis free_valid_block:
  forall m b m' b',
  free m b = Some m' -> b' <> b -> (valid_block m' b' <-> valid_block m b').
Hypothesis valid_block_free:
  forall m b,
  valid_block m b -> exists m', free m b = Some m'.

Variable bounds: mem -> block -> Z*Z.

Hypothesis alloc_result_bounds:
  forall m lo hi b m',
  alloc m lo hi = Some(b, m') -> bounds m' b = (lo, hi).
Hypothesis alloc_bounds_inv:
  forall m lo hi b m' b',
  alloc m lo hi = Some(b, m') -> b' <> b -> bounds m' b' = bounds m b'.
Hypothesis store_bounds_inv:
  forall ty m b ofs v m' b',
  store ty m b ofs v = Some m' -> bounds m' b' = bounds m b'.
Hypothesis free_bounds_inv:
  forall m b m' b',
  free m b = Some m' -> b' <> b -> bounds m' b' = bounds m b'.

Definition valid_pointer (ty: memtype) (m: mem) (b: block) (ofs: Z) : Prop :=
  valid_block m b
  /\ (alignof ty | ofs)
  /\ fst (bounds m b) <= ofs
  /\ ofs + sizeof ty <= snd (bounds m b).

Hypothesis valid_pointer_store:
  forall ty m b ofs v,
  valid_pointer ty m b ofs ->
  exists m', store ty m b ofs v = Some m'.

(** Additional properties specific to the concrete memory model. *)

Hypothesis valid_pointer_load:
  forall ty m b ofs,
  valid_pointer ty m b ofs ->
  exists v, load ty m b ofs = Some v.

Hypothesis store_valid_pointer:
  forall ty m b ofs v m',
  store ty m b ofs v = Some m' -> valid_pointer ty m b ofs.

Hypothesis load_valid_pointer:
  forall ty m b ofs v,
  load ty m b ofs = Some v -> valid_pointer ty m b ofs.

Hypothesis load_alloc_same:
  forall m lo hi b m' ty ofs v,
  alloc m lo hi = Some (b, m') ->
  load ty m' b ofs = Some v ->
  v = vundef.

Hypothesis load_store_mismatch:
  forall ty m b ofs v m' ty' v',
  store ty m b ofs v = Some m' ->
  ~(compat ty ty') ->
  load ty' m' b ofs = Some v' ->
  v' = vundef.

Hypothesis load_store_overlap:
  forall ty m b ofs v m' ty' ofs' v',
  store ty m b ofs v = Some m' ->
  ofs' <> ofs -> ofs' + sizeof ty' > ofs -> ofs + sizeof ty > ofs' ->
  load ty' m' b ofs' = Some v' ->
  v' = vundef.

Variable fresh_block: mem -> block -> Prop.

Hypothesis fresh_valid_block_exclusive:
  forall m b,
  fresh_block m b -> valid_block m b -> False.

Hypothesis alloc_fresh_block:
  forall m lo hi b m' b',
  alloc m lo hi = Some(b, m') -> 
  (fresh_block m' b' <-> b <> b' /\ fresh_block m b').

Hypothesis alloc_fresh_block_2:
  forall m lo hi b m',
  alloc m lo hi = Some(b, m') -> fresh_block m b.

Hypothesis store_fresh_block:
  forall m chunk b ofs v m' b',
  store chunk m b ofs v = Some m' ->
  (fresh_block m' b' <-> fresh_block m b').

Hypothesis free_fresh_block:
  forall m b m' b',
  free m b = Some m' ->
  (fresh_block m' b' <-> fresh_block m b').

Definition same_domain (m1 m2: mem) : Prop :=
  forall b, fresh_block m1 b <-> fresh_block m2 b.

Hypothesis alloc_same_domain:
  forall m1 lo1 hi1 b1 m1' m2 lo2 hi2 b2 m2',
  alloc m1 lo1 hi1 = Some(b1, m1') ->
  alloc m2 lo2 hi2 = Some(b2, m2') ->
  same_domain m1 m2 ->
  b1 = b2 /\ same_domain m1' m2'.

Hypothesis free_not_valid_block:
  forall m b m',
  free m b = Some m' -> ~(valid_block m' b).

Hypothesis free_same_bounds:
  forall m b m',
  free m b = Some m' ->
  fst(bounds m' b) = snd(bounds m' b).

End REF_GEN_MEM.

(** Derived properties of the concrete memory model. *)

Module Ref_Gen_Mem_Facts(M: REF_GEN_MEM).

Import M.
Module MF := Gen_Mem_Facts(M).
Import MF.

Lemma store_valid_pointer_2:
  forall ty m b ofs v m',
  store ty m b ofs v = Some m' -> valid_pointer ty m' b ofs.
Proof.
  intros. rewrite (store_valid_pointer_inv _ _ _ _ _ _ ty b ofs H).
  eapply store_valid_pointer; eauto.
Qed.

Lemma load_alloc_same_2:
  forall m lo hi b m' ty ofs,
  alloc m lo hi = Some (b, m') ->
  (alignof ty | ofs) -> lo <= ofs -> ofs + sizeof ty <= hi ->
  load ty m' b ofs = Some vundef.
Proof.
  intros. 
  assert (valid_pointer ty m' b ofs).
    split. rewrite (alloc_valid_block _ _ _ _ _ b H). auto.
    rewrite (alloc_result_bounds _ _ _ _ _ H). simpl; tauto.
  destruct (valid_pointer_load _ _ _ _ H3) as [v LOAD].
  assert (v = vundef).
    eapply load_alloc_same; eauto.
  congruence.
Qed. 

Lemma load_store_mismatch_2:
  forall ty m b ofs v m' ty',
  store ty m b ofs v = Some m' ->
  ~(compat ty ty') ->
  valid_pointer ty' m b ofs ->
  load ty' m' b ofs = Some vundef.
Proof.
  intros.
  assert (valid_pointer ty' m' b ofs).
    rewrite (MF.store_valid_pointer_inv _ _ _ _ _ _ ty' b ofs H). auto.
  destruct (valid_pointer_load _ _ _ _ H2) as [v' LOAD].
  assert (v' = vundef).
    eapply load_store_mismatch; eauto.
  congruence.
Qed.

Lemma load_store_overlap_2:
  forall ty m b ofs v m' ty' ofs',
  store ty m b ofs v = Some m' ->
  ofs' <> ofs -> ofs' + sizeof ty' > ofs -> ofs + sizeof ty > ofs' ->
  valid_pointer ty' m b ofs' ->
  load ty' m' b ofs' = Some vundef.
Proof.
  intros.
  assert (valid_pointer ty' m' b ofs').
    rewrite (MF.store_valid_pointer_inv _ _ _ _ _ _ ty' b ofs' H). auto.
  destruct (valid_pointer_load _ _ _ _ H4) as [v' LOAD].
  assert (v' = vundef).
    eapply load_store_overlap; eauto.
  congruence.
Qed.

Inductive load_store_cases 
      (ty1: memtype) (b1: block) (ofs1: Z)
      (ty2: memtype) (b2: block) (ofs2: Z) : Set :=
  | lsc_similar:
      b1 = b2 -> ofs1 = ofs2 -> compat ty1 ty2 ->
      load_store_cases ty1 b1 ofs1 ty2 b2 ofs2
  | lsc_other:
      b1 <> b2 \/ ofs2 + sizeof ty2 <= ofs1 \/ ofs1 + sizeof ty1 <= ofs2 ->
      load_store_cases ty1 b1 ofs1 ty2 b2 ofs2
  | lsc_overlap:
      b1 = b2 -> ofs1 <> ofs2 -> ofs2 + sizeof ty2 > ofs1 -> ofs1 + sizeof ty1 > ofs2 ->
      load_store_cases ty1 b1 ofs1 ty2 b2 ofs2
  | lsc_mismatch:
      b1 = b2 -> ofs1 = ofs2 -> ~compat ty1 ty2 ->
      load_store_cases ty1 b1 ofs1 ty2 b2 ofs2.

Lemma load_store_classification:
  forall (ty1: memtype) (b1: block) (ofs1: Z)
         (ty2: memtype) (b2: block) (ofs2: Z),
  load_store_cases ty1 b1 ofs1 ty2 b2 ofs2.
Proof.
  intros. destruct (eq_block b1 b2).
  destruct (zeq ofs1 ofs2).
  destruct (compat_dec ty1 ty2).
  apply lsc_similar; auto.
  apply lsc_mismatch; auto.
  destruct (zle (ofs2 + sizeof ty2) ofs1).
  apply lsc_other. tauto.
  destruct (zle (ofs1 + sizeof ty1) ofs2).
  apply lsc_other. tauto.
  apply lsc_overlap; auto.
  apply lsc_other; tauto.
Qed.

Lemma load_store_characterization:
  forall ty m1 b ofs v m2 ty' b' ofs',
  store ty m1 b ofs v = Some m2 ->
  valid_pointer ty' m1 b' ofs' ->
  load ty' m2 b' ofs' =
    match load_store_classification ty b ofs ty' b' ofs' with
    | lsc_similar _ _ _ => Some (convert ty' v)
    | lsc_other _ => load ty' m1 b' ofs'
    | lsc_overlap _ _ _ _ => Some vundef
    | lsc_mismatch _ _ _ => Some vundef
    end.
Proof.
  intros.
  assert (valid_pointer ty' m2 b' ofs').
    rewrite (MF.store_valid_pointer_inv _ _ _ _ _ _ ty' b' ofs' H). auto.
  destruct (valid_pointer_load _ _ _ _ H1) as [v' LOAD].
  destruct (load_store_classification ty b ofs ty' b' ofs').
  subst b' ofs'. eapply load_store_same; eauto.
  eapply load_store_disjoint; eauto. intuition.
  subst b'. rewrite LOAD. f_equal. 
  eapply load_store_overlap; eauto. 
  subst b' ofs'. rewrite LOAD. f_equal. 
  eapply load_store_mismatch; eauto.
Qed.

Lemma store_same_domain:
  forall ty1 m1 b1 ofs1 v1 m1' ty2 m2 b2 ofs2 v2 m2',
  store ty1 m1 b1 ofs1 v1 = Some m1' ->
  store ty2 m2 b2 ofs2 v2 = Some m2' ->
  same_domain m1 m2 ->
  same_domain m1' m2'.
Proof.
  intros; red; intros.
  rewrite (store_fresh_block _ _ _ _ _ _ b H).
  rewrite (store_fresh_block _ _ _ _ _ _ b H0).
  apply H1.
Qed.

Lemma free_same_domain:
  forall m1 b m1' m2 m2',
  free m1 b = Some m1' ->
  free m2 b = Some m2' ->
  same_domain m1 m2 ->
  same_domain m1' m2'.
Proof.
  unfold same_domain; intros.
  rewrite (free_fresh_block _ _ _ b0 H).
  rewrite (free_fresh_block _ _ _ b0 H0).
  auto.
Qed.

Lemma free_not_valid_pointer:
  forall m b m',
  free m b = Some m' ->
  forall ty ofs, ~(valid_pointer ty m' b ofs).
Proof.
  intros; red; intros. destruct H0 as [A [B [C D]]].
  rewrite (free_same_bounds _ _ _ H) in C; simpl in C.
  generalize (sizeof_pos ty). omega.
Qed.

End Ref_Gen_Mem_Facts.

(** An implementation of the concrete memory model *)

Definition update (A: Set) (x: Z) (v: A) (f: Z -> A): Z -> A :=
  fun y => if zeq y x then v else f y.

Implicit Arguments update [A].

Lemma update_s:
  forall (A: Set) (x: Z) (v: A) (f: Z -> A),
  update x v f x = v.
Proof.
  intros; unfold update; destruct (zeq x x); congruence.
Qed.

Lemma update_o:
  forall (A: Set) (x: Z) (v: A) (f: Z -> A) (y: Z),
  y <> x -> update x v f y = f y.
Proof.
  intros; unfold update; destruct (zeq y x); congruence.
Qed.

Module Concrete_Mem <: REF_GEN_MEM.

Definition block := Z.

Lemma eq_block: forall (b1 b2: block), {b1=b2} + {b1<>b2}.
Proof zeq.

Definition content := option (memtype * val).

Record mem_ : Set := mkmem {
  nextblock: Z;
  bounds: block -> Z*Z;
  freed: block -> bool;
  contents: block -> Z -> content
}.

Definition mem := mem_.

Definition empty: mem :=
  mkmem 1 
        (fun (b: block) => (0, 0)) 
        (fun (b: block) => false)
        (fun (b: block) (ofs: Z) => None).

Definition fresh_block (m: mem) (b: block) : Prop :=
  b >= nextblock m.

Definition valid_block (m: mem) (b: block) : Prop :=
  b < nextblock m /\ freed m b = false.

Lemma valid_block_dec:
  forall m b, {valid_block m b} + {~valid_block m b}.
Proof.
  intros; unfold valid_block. destruct (zlt b (nextblock m)).
  destruct (freed m b). 
  right; red; intros [A B]; congruence.
  left; auto.
  right; red; intros [A B]; omega.
Qed.

Definition valid_pointer (ty: memtype) (m: mem) (b: block) (ofs: Z) : Prop :=
  valid_block m b
  /\ (alignof ty | ofs)
  /\ fst (bounds m b) <= ofs
  /\ ofs + sizeof ty <= snd (bounds m b).

Remark Zdivide_Zmod:
  forall a b, b > 0 -> ((b | a) <-> Zmod a b = 0).
Proof.
  intros; split; intros.
  apply Z_div_exact_1. auto. inv H0. rewrite Z_div_mult; auto. ring.
  exists (a / b).
  transitivity (b * (a / b) + (a mod b)). apply Z_div_mod_eq; auto.
  transitivity (b * (a / b)). omega. 
  ring.
Qed.

Lemma aligned_dec:
  forall ty ofs, {(alignof ty | ofs)} + {~(alignof ty | ofs)}.
Proof.
  intros. generalize (Zdivide_Zmod ofs (alignof ty) (alignof_pos ty)); intro.
  destruct (zeq (Zmod ofs (alignof ty)) 0).
  left. rewrite H. auto.
  right. rewrite H. auto.
Qed.

Lemma valid_pointer_dec:
  forall ty m b ofs, {valid_pointer ty m b ofs} + {~valid_pointer ty m b ofs}.
Proof.
  intros. unfold valid_pointer.
  destruct (valid_block_dec m b).
  destruct (aligned_dec ty ofs).
  destruct (zle (fst (bounds m b)) ofs).
  destruct (zle (ofs + sizeof ty) (snd (bounds m b))).
  left; auto.
  right. red. intros [A [B [C D]]]. omega.
  right. red. intros [A [B [C D]]]. omega.
  right. tauto.
  right. tauto.
Qed.

Definition nat_of_Z (z: Z) : nat :=
  match z with
  | Z0 => O
  | Zpos p => nat_of_P p
  | Zneg p => O
  end.

Lemma nat_of_Z_eq:
  forall z, z >= 0 -> Z_of_nat (nat_of_Z z) = z.
Proof.
  intros. destruct z; simpl.
  auto.
  symmetry. apply Zpos_eq_Z_of_nat_o_nat_of_P.
  compute in H. congruence.
Qed.

Fixpoint check_cont (f: Z -> content) (ofs: Z) (n: nat) {struct n} : bool :=
  match n with
  | O => true
  | S n' =>
    match f ofs with
    | None => check_cont f (ofs + 1) n'
    | _ => false
    end
  end.

Lemma check_cont_charact:
  forall f n ofs,
  if check_cont f ofs n
  then (forall i, ofs <= i < ofs + Z_of_nat n -> f i = None)
  else (exists i, ofs <= i < ofs + Z_of_nat n /\ f i <> None).
Proof.
  induction n; intros.
  simpl. intros. elimtype False; omega.
  rewrite inj_S. simpl. 
  case_eq (f ofs); intros.
  exists ofs. split. omega. congruence.
  generalize (IHn (ofs + 1)). destruct (check_cont f (ofs + 1)).
  intros. assert (i = ofs \/ ofs + 1 <= i < (ofs + 1) + (Z_of_nat n)) by omega. 
  destruct H2. congruence.
  apply H0. auto.  
  intros [i [A B]]. exists i; split. omega. auto. 
Qed.

Lemma check_cont_exten:
  forall f1 f2 n ofs,
  (forall i, ofs <= i < ofs + Z_of_nat n -> f2 i = f1 i) ->
  check_cont f2 ofs n = check_cont f1 ofs n.
Proof.
  induction n; intros; simpl.
  auto.
  rewrite inj_S in H.
  rewrite H. destruct (f1 ofs); auto. apply IHn. 
  intros. apply H. omega. omega. 
Qed. 

Definition load_contents (ty: memtype) (f: Z -> content) (ofs: Z) : val :=
  match f ofs with
  | Some(ty', v) =>
      if compat_dec ty' ty then
        if check_cont f (ofs + 1) (nat_of_Z (sizeof ty - 1))
        then convert ty v
        else vundef
      else vundef
  | _ => vundef
  end.

Lemma load_contents_exten:
  forall f1 f2 ty ofs,
  (forall i, ofs <= i < ofs + sizeof ty -> f2 i = f1 i) ->
  load_contents ty f2 ofs = load_contents ty f1 ofs.
Proof.
  intros. unfold load_contents.
  rewrite H. destruct (f1 ofs). 
  destruct p as [ty' v].
  destruct (compat_dec ty' ty); auto.
  rewrite (check_cont_exten f1 f2). 
  destruct (check_cont f1 (ofs + 1) (nat_of_Z (sizeof ty - 1))); auto.
  intros. apply H. rewrite nat_of_Z_eq in H0. omega. 
  generalize (sizeof_pos ty); omega.
  auto.
  generalize (sizeof_pos ty); omega.
Qed.

Lemma load_contents_1:
  forall ty f ofs ty' v,
  f ofs = Some(ty', v) ->
  compat ty' ty ->
  (forall i, ofs + 1 <= i < ofs + sizeof ty -> f i = None) ->
  load_contents ty f ofs = convert ty v.
Proof.
  intros. unfold load_contents.
  rewrite H. destruct (compat_dec ty' ty). 2:contradiction.
  generalize (check_cont_charact f (nat_of_Z (sizeof ty - 1)) (ofs + 1)).
  destruct (check_cont f (ofs + 1) (nat_of_Z (sizeof ty - 1))).
  auto.
  intros [i [A B]]. elim B. apply H1.
  rewrite nat_of_Z_eq in A. omega. 
  generalize (sizeof_pos ty). omega.
Qed.

Lemma load_contents_2:
  forall ty f ofs,
  f ofs = None ->
  load_contents ty f ofs = vundef.
Proof.
  intros. unfold load_contents. rewrite H. auto.
Qed.

Lemma load_contents_3:
  forall ty f ofs ty' v,
  f ofs = Some(ty', v) ->
  ~compat ty' ty ->
  load_contents ty f ofs = vundef.
Proof.
  intros; unfold load_contents. rewrite H. 
  destruct (compat_dec ty' ty). contradiction. auto.
Qed.

Lemma load_contents_4:
  forall ty f ofs i,
  ofs + 1 <= i < ofs + sizeof ty -> f i <> None ->
  load_contents ty f ofs = vundef.
Proof.
  intros. unfold load_contents.
  destruct (f ofs). destruct p as [ty' v]. 
  destruct (compat_dec ty' ty); auto.
  generalize (check_cont_charact f (nat_of_Z (sizeof ty - 1)) (ofs + 1)).
  destruct (check_cont f (ofs + 1) (nat_of_Z (sizeof ty - 1))).
  intro. elim H0. apply H1. rewrite nat_of_Z_eq. omega. 
  generalize (sizeof_pos ty). omega.
  auto.
  auto.
Qed.

Fixpoint set_cont (f: Z -> content) (ofs: Z) (n: nat) {struct n} : Z -> content :=
  match n with
  | O => f
  | S n' => set_cont (update ofs None f) (ofs + 1) n'
  end.

Lemma set_cont_outside:
  forall n f ofs i,
  i < ofs \/ i >= ofs + Z_of_nat n -> set_cont f ofs n i = f i.
Proof.
  induction n; intros; simpl.
  auto.
  rewrite inj_S in H. rewrite IHn. apply update_o. omega. omega. 
Qed.

Lemma set_cont_inside:
  forall n f ofs i,
  ofs <= i < ofs + Z_of_nat n -> set_cont f ofs n i = None.
Proof.
  induction n; intros; simpl.
  simpl in H. elimtype False; omega.
  rewrite inj_S in H.
  assert (i = ofs \/ ofs + 1 <= i < (ofs + 1) + Z_of_nat n) by omega.
  destruct H0. subst i. rewrite set_cont_outside. apply update_s. omega. 
  apply IHn. omega. 
Qed. 

Definition store_contents (f: Z -> content) (ty: memtype) (ofs: Z) (v: val): Z -> content :=
  set_cont (update ofs (Some (ty, v)) f) (ofs + 1) (nat_of_Z (sizeof ty - 1)).

Lemma store_contents_at:
  forall f ty ofs v,
  store_contents f ty ofs v ofs = Some (ty, v).
Proof.
  intros; unfold store_contents. 
  rewrite set_cont_outside. apply update_s. omega.
Qed.

Lemma store_contents_cont:
  forall f ty ofs v i,
  ofs < i < ofs + sizeof ty ->
  store_contents f ty ofs v i = None.
Proof.
  intros; unfold store_contents.
  apply set_cont_inside. rewrite nat_of_Z_eq. omega. 
  generalize (sizeof_pos ty); omega.
Qed.

Lemma store_contents_outside:
  forall f ty ofs v i,
  i < ofs \/ i >= ofs + sizeof ty ->
  store_contents f ty ofs v i = f i.
Proof.
  intros; unfold store_contents.
  rewrite set_cont_outside. apply update_o. 
  generalize (sizeof_pos ty). omega.
  rewrite nat_of_Z_eq. omega. 
  generalize (sizeof_pos ty); omega.
Qed.

Lemma load_store_contents_same:
  forall f ty ty' ofs v,
  compat ty ty' ->
  load_contents ty' (store_contents f ty ofs v) ofs = convert ty' v.
Proof.
  intros. apply load_contents_1 with ty.
  apply store_contents_at. auto. 
  intros. apply store_contents_cont. 
  rewrite <- (compat_sizeof _ _ H). omega.
Qed.

Lemma load_store_contents_disjoint:
  forall f ty ty' ofs ofs' v,
  ofs' + sizeof ty' <= ofs \/ ofs + sizeof ty <= ofs' ->
  load_contents ty' (store_contents f ty ofs v) ofs' =
  load_contents ty' f ofs'.
Proof.
  intros. apply load_contents_exten. 
  intros. apply store_contents_outside. omega. 
Qed.

Lemma load_store_contents_mismatch:
  forall f ty ty' ofs v,
  ~compat ty ty' ->
  load_contents ty' (store_contents f ty ofs v) ofs = vundef.
Proof.
  intros. eapply load_contents_3; eauto.
  apply store_contents_at.  
Qed.

Lemma load_store_contents_overlap:
  forall f ty ty' ofs ofs' v,
  ofs' <> ofs -> ofs' + sizeof ty' > ofs -> ofs + sizeof ty > ofs' ->
  load_contents ty' (store_contents f ty ofs v) ofs' = vundef.
Proof.
  intros. generalize (sizeof_pos ty); generalize (sizeof_pos ty'); intros.
  assert (ofs < ofs' < ofs + sizeof ty
          \/ ofs' < ofs < ofs' + sizeof ty') by omega.
  destruct H4.
  (* case 1: load at ofs' reads back a Cont put by store *)
  apply load_contents_2. 
  rewrite store_contents_cont. auto. auto.
  (* case 2: load at ofs' + something reads back the Data put by store *)
  apply load_contents_4 with ofs. omega. 
  rewrite store_contents_at. congruence.
Qed.

Parameter enough_free_memory: mem -> Z -> bool.

(* Definition alloc (m: mem) (lo hi: Z) : option (block * mem) := *)
(*   if enough_free_memory m (hi - lo) *)
(*   then Some(nextblock m, *)
(*             mkmem (nextblock m + 1) *)
(*              (update (nextblock m) (lo, hi) (bounds m)) *)
(*              (update (nextblock m) false (freed m)) *)
(*              (update (nextblock m) (fun (ofs: Z) => None) (contents m))) *)
(*   else None. *)

Definition load (ty: memtype) (m: mem) (b: block) (ofs: Z) : option val :=
  if valid_pointer_dec ty m b ofs
  then Some (load_contents ty (contents m b) ofs)
  else None.

Definition store (ty: memtype) (m: mem) (b: block) (ofs: Z) (v: val) : option mem :=
  if valid_pointer_dec ty m b ofs
  then Some(mkmem (nextblock m)
                  (bounds m)
                  (freed m)
                  (update b (store_contents (contents m b) ty ofs v) (contents m)))
  else None.

Definition free (m: mem) (b: block) : option mem :=
  if freed m b
  then None
  else Some(mkmem (nextblock m)
                  (update b (0,0) (bounds m))
                  (update b true (freed m))
                  (contents m)).

Lemma alloc_result_bounds:
  forall m lo hi b m',
  alloc m lo hi = Some(b, m') -> bounds m' b = (lo, hi).
Proof.
  unfold alloc; intros.
  destruct (enough_free_memory m (hi-lo)); inv H; simpl.
  apply update_s.
Qed.

Lemma alloc_bounds_inv:
  forall m lo hi b m' b',
  alloc m lo hi = Some(b, m') -> b' <> b -> bounds m' b' = bounds m b'.
Proof.
  unfold alloc; intros.
  destruct (enough_free_memory m (hi-lo)); inv H; simpl.
  apply update_o. auto.
Qed.

Lemma store_bounds_inv:
  forall ty m b ofs v m' b',
  store ty m b ofs v = Some m' -> bounds m' b' = bounds m b'.
Proof.
  unfold store; intros.
  destruct (valid_pointer_dec ty m b ofs); inv H; simpl.
  auto.
Qed.

Lemma free_bounds_inv:
  forall m b m' b',
  free m b = Some m' -> b' <> b -> bounds m' b' = bounds m b'.
Proof.
  unfold free; intros. destruct (freed m b); inv H; simpl. apply update_o. auto.
Qed.

Lemma fresh_valid_block_exclusive:
  forall m b,
  fresh_block m b -> valid_block m b -> False.
Proof.
  unfold fresh_block, valid_block; intros.
  destruct H0. omega.
Qed.

Lemma alloc_fresh_block:
  forall m lo hi b m' b',
  alloc m lo hi = Some(b, m') -> 
  (fresh_block m' b' <-> b <> b' /\ fresh_block m b').
Proof.
  unfold alloc, fresh_block; intros.
  destruct (enough_free_memory m (hi-lo)); inv H; simpl.
  unfold block. split; intros; omega.
Qed.

Lemma alloc_fresh_block_2:
  forall m lo hi b m',
  alloc m lo hi = Some(b, m') -> fresh_block m b.
Proof.
  unfold alloc, fresh_block; intros.
  destruct (enough_free_memory m (hi-lo)); inv H; simpl.
  omega.
Qed.

Lemma store_inversion:
  forall ty m b ofs v m',
  store ty m b ofs v = Some m' ->
  valid_pointer ty m b ofs /\
  m' = mkmem (nextblock m)
             (bounds m)
             (freed m)
             (update b (store_contents (contents m b) ty ofs v) (contents m)).
Proof.
  unfold store; intros. 
  destruct (valid_pointer_dec ty m b ofs); inv H. auto.
Qed.

Lemma store_fresh_block:
  forall m chunk b ofs v m' b',
  store chunk m b ofs v = Some m' ->
  (fresh_block m' b' <-> fresh_block m b').
Proof.
  intros. destruct (store_inversion _ _ _ _ _ _ H) as [A B].
  unfold fresh_block; rewrite B; simpl. tauto.
Qed.

Lemma free_fresh_block:
  forall m b m' b',
  free m b = Some m' ->
  (fresh_block m' b' <-> fresh_block m b').
Proof.
  unfold free. intros. destruct (freed m b); inv H; unfold fresh_block; simpl. tauto.
Qed.

Lemma alloc_valid_block:
  forall m lo hi b m' b',
  alloc m lo hi = Some(b, m') ->
  (valid_block m' b' <-> b' = b \/ valid_block m b').
Proof.
  unfold alloc, valid_block; intros.
  destruct (enough_free_memory m (hi-lo)); inv H; simpl.
  unfold update. destruct (zeq b' (nextblock m)).
  subst b'; intuition.
  intuition. 
Qed.

Lemma alloc_not_valid_block:
  forall m lo hi b m',
  alloc m lo hi = Some(b, m') -> ~(valid_block m b).
Proof.
  intros; red; intros. eapply fresh_valid_block_exclusive; eauto.
  eapply alloc_fresh_block_2; eauto.
Qed.

Lemma load_valid_block:
  forall ty m b ofs v,
  load ty m b ofs = Some v -> valid_block m b.
Proof.
  unfold load; intros. destruct (valid_pointer_dec ty m b); inv H.
  inv v0; auto.
Qed.

Lemma store_valid_block:
  forall ty m b ofs v m',
  store ty m b ofs v = Some m' -> valid_block m b.
Proof.
  unfold store; intros. destruct (valid_pointer_dec ty m b); inv H.
  inv v0; auto.
Qed.

Lemma store_valid_block_inv:
  forall ty m b ofs v m' b',
  store ty m b ofs v = Some m' -> (valid_block m' b' <-> valid_block m b').
Proof.
  unfold store, valid_block; intros.
  destruct (valid_pointer_dec ty m b); inv H; simpl.
  tauto.
Qed.

Lemma free_valid_block:
  forall m b m' b',
  free m b = Some m' -> b' <> b -> (valid_block m' b' <-> valid_block m b').
Proof.
  unfold free; intros. destruct (freed m b); inv H; unfold valid_block; simpl.
  rewrite update_o. tauto. auto.
Qed.

Lemma store_valid_pointer_inv:
  forall ty m b ofs v m' ty' b' ofs',
  store ty m b ofs v = Some m' ->
  (valid_pointer ty' m' b' ofs' <-> valid_pointer ty' m b' ofs').
Proof.
  intros. unfold valid_pointer. 
  rewrite (store_bounds_inv _ _ _ _ _ _ b' H).
  rewrite (store_valid_block_inv _ _ _ _ _ _ b' H). 
  tauto.
Qed. 

Lemma alloc_valid_pointer_inv:
  forall m lo hi b m' ty b' ofs,
  alloc m lo hi = Some(b, m') -> b' <> b ->
  (valid_pointer ty m b' ofs <-> valid_pointer ty m' b' ofs).
Proof.
  intros. unfold valid_pointer. 
  rewrite (alloc_valid_block _ _ _ _ _ b' H). 
  rewrite (alloc_bounds_inv _ _ _ _ _ _ H H0). tauto.
Qed.

Lemma free_valid_pointer_inv:
  forall m b m' ty b' ofs,
  free m b = Some m' -> b' <> b ->
  (valid_pointer ty m' b' ofs <-> valid_pointer ty m b' ofs).
Proof.
  intros. unfold valid_pointer.
  rewrite (free_bounds_inv _ _ _ _ H H0).
  rewrite (free_valid_block _ _ _ _ H H0).
  tauto.
Qed.

Lemma load_alloc_other:
  forall m lo hi b m' ty b' ofs,
  alloc m lo hi = Some (b, m') ->
  b' <> b ->
  load ty m' b' ofs = load ty m b' ofs.
Proof.
  intros. unfold load. 
  destruct (valid_pointer_dec ty m b' ofs). 
  rewrite (alloc_valid_pointer_inv _ _ _ _ _ ty _ ofs H H0) in v.
  destruct (valid_pointer_dec ty m' b' ofs); try contradiction.
  f_equal. f_equal.
  unfold alloc in H; destruct (enough_free_memory m (hi-lo)); inv H; simpl.
  apply update_o; auto.
  rewrite (alloc_valid_pointer_inv _ _ _ _ _ ty _ ofs H H0) in n.
  destruct (valid_pointer_dec ty m' b' ofs); try contradiction. auto.
Qed.

Lemma valid_pointer_compat:
  forall ty m b ofs ty',
  compat ty ty' ->
  (valid_pointer ty m b ofs <-> valid_pointer ty' m b ofs).
Proof.
  unfold valid_pointer; intros. 
  rewrite (compat_sizeof _ _ H). rewrite (compat_alignof _ _ H).
  tauto.
Qed.

Lemma load_store_same:
  forall ty m b ofs v m' ty',
  store ty m b ofs v = Some m' ->
  compat ty ty' ->
  load ty' m' b ofs = Some (convert ty' v).
Proof.
  intros. destruct (store_inversion _ _ _ _ _ _ H).
  unfold load. destruct (valid_pointer_dec ty' m' b ofs).  
  f_equal. rewrite H2; simpl. rewrite update_s. apply load_store_contents_same; auto.
  elim n.
  rewrite <- (valid_pointer_compat ty m' b ofs ty' H0). 
  rewrite (store_valid_pointer_inv _ _ _ _ _ _ ty b ofs H). auto.
Qed.

Lemma load_store_disjoint:
  forall ty m b ofs v m' ty' b' ofs',
  store ty m b ofs v = Some m' ->
  b' <> b \/ ofs' + sizeof ty' <= ofs \/ ofs + sizeof ty <= ofs' ->
  load ty' m' b' ofs' = load ty' m b' ofs'.
Proof.
  intros. destruct (store_inversion _ _ _ _ _ _ H).
  unfold load. 
  destruct (valid_pointer_dec ty' m' b' ofs'). 
  rewrite (store_valid_pointer_inv _ _ _ _ _ _ ty' b' ofs' H) in v0.
  destruct (valid_pointer_dec ty' m b' ofs'); try contradiction.
  f_equal. rewrite H2; simpl; unfold update. destruct (zeq b' b).
  subst b'. apply load_store_contents_disjoint. destruct H0. congruence. auto.
  auto.
  rewrite (store_valid_pointer_inv _ _ _ _ _ _ ty' b' ofs' H) in n.
  destruct (valid_pointer_dec ty' m b' ofs'); try contradiction. auto.
Qed.
 
Lemma load_free_other:
  forall m b m' ty b' ofs,
  free m b = Some m' ->
  b' <> b ->
  load ty m' b' ofs = load ty m b' ofs.
Proof.
  intros. unfold load. destruct (valid_pointer_dec ty m' b' ofs).
  rewrite (free_valid_pointer_inv _ _ _ ty b' ofs H H0) in v.
  destruct (valid_pointer_dec ty m b' ofs); try contradiction.
  f_equal. f_equal.
  unfold free in H; destruct (freed m b); inv H; simpl. auto.
  rewrite (free_valid_pointer_inv _ _ _ ty b' ofs H H0) in n.
  destruct (valid_pointer_dec ty m b' ofs); try contradiction. auto.
Qed.

Lemma load_alloc_same:
  forall m lo hi b m' ty ofs v,
  alloc m lo hi = Some (b, m') ->
  load ty m' b ofs = Some v ->
  v = vundef.
Proof.
  unfold alloc, load; intros.
  destruct (valid_pointer_dec ty m' b ofs); inv H0.
  destruct (enough_free_memory m (hi-lo)); inv H; simpl.
  rewrite update_s. apply load_contents_2. auto.
Qed.

Lemma load_store_mismatch:
  forall ty m b ofs v m' ty' v',
  store ty m b ofs v = Some m' ->
  ~(compat ty ty') ->
  load ty' m' b ofs = Some v' ->
  v' = vundef.
Proof.
  unfold load, store; intros. 
  destruct (valid_pointer_dec ty' m' b ofs); inv H1. 
  destruct (valid_pointer_dec ty m b ofs); inversion H. 
  simpl. rewrite update_s. 
  apply load_store_contents_mismatch; auto.
Qed.

Lemma load_store_overlap:
  forall ty m b ofs v m' ty' ofs' v',
  store ty m b ofs v = Some m' ->
  ofs' <> ofs -> ofs' + sizeof ty' > ofs -> ofs + sizeof ty > ofs' ->
  load ty' m' b ofs' = Some v' ->
  v' = vundef.
Proof.
  unfold load, store; intros. 
  destruct (valid_pointer_dec ty' m' b ofs'); inv H3. 
  destruct (valid_pointer_dec ty m b ofs); inversion H. 
  simpl. rewrite update_s. 
  apply load_store_contents_overlap; auto.
Qed.

Definition same_domain (m1 m2: mem) : Prop :=
  forall b, fresh_block m1 b <-> fresh_block m2 b.

Lemma same_domain_same_nextblock:
  forall m1 m2, same_domain m1 m2 -> nextblock m2 = nextblock m1.
Proof.
  unfold same_domain, fresh_block; intros.
  assert (nextblock m2 >= nextblock m1).
    rewrite H. omega.
  assert (nextblock m1 >= nextblock m2).
    rewrite <- H. omega.
  unfold block. omega.
Qed. 

Lemma alloc_same_domain:
  forall m1 lo1 hi1 b1 m1' m2 lo2 hi2 b2 m2',
  alloc m1 lo1 hi1 = Some(b1, m1') ->
  alloc m2 lo2 hi2 = Some(b2, m2') ->
  same_domain m1 m2 ->
  b1 = b2 /\ same_domain m1' m2'.
Proof.
  unfold alloc; intros.
  destruct (enough_free_memory m1 (hi1-lo1)); inv H; simpl.
  destruct (enough_free_memory m2 (hi2-lo2)); inv H0; simpl.
  unfold same_domain, fresh_block; simpl.
  rewrite (same_domain_same_nextblock _ _ H1). 
  split. auto. intros. tauto.
Qed.

Lemma valid_block_free:
  forall m b,
  valid_block m b -> exists m', free m b = Some m'.
Proof.
  intros. destruct H. unfold free. rewrite H0.
  econstructor. reflexivity.
Qed.

Lemma valid_pointer_store:
  forall ty m b ofs v,
  valid_pointer ty m b ofs ->
  exists m', store ty m b ofs v = Some m'.
Proof.
  intros. unfold store. 
  destruct (valid_pointer_dec ty m b ofs). 
  econstructor; reflexivity.
  contradiction.
Qed.

Lemma store_valid_pointer:
  forall ty m b ofs v m',
  store ty m b ofs v = Some m' -> valid_pointer ty m b ofs.
Proof.
  intros. destruct (store_inversion _ _ _ _ _ _ H). auto.
Qed.

Lemma valid_pointer_load:
  forall ty m b ofs,
  valid_pointer ty m b ofs ->
  exists v, load ty m b ofs = Some v.
Proof.
  intros. unfold load. destruct (valid_pointer_dec ty m b ofs). 
  econstructor. reflexivity.
  contradiction.
Qed.

Lemma load_valid_pointer:
  forall ty m b ofs v,
  load ty m b ofs = Some v -> valid_pointer ty m b ofs.
Proof.
  unfold load; intros. destruct (valid_pointer_dec ty m b ofs). 
  auto. discriminate.
Qed.

Lemma free_not_valid_block:
  forall m b m',
  free m b = Some m' ->
  ~(valid_block m' b).
Proof.
  unfold free, valid_block; intros. destruct (freed m b); inv H; simpl. 
  rewrite update_s. red; intros [A B]; congruence.
Qed.

Lemma free_same_bounds:
  forall m b m',
  free m b = Some m' ->
  fst(bounds m' b) = snd(bounds m' b).
Proof.
  unfold free; intros. destruct (freed m b); inv H; simpl. 
  rewrite update_s. auto.
Qed.

End Concrete_Mem.

(** * Section 5: Relating two memory states before and after program transformation *)

Module Rel_Mem(M: REF_GEN_MEM).

Module MF := Gen_Mem_Facts(M).
Module RMF := Ref_Gen_Mem_Facts(M).
Import M.
Import MF.
Import RMF.

(** ** Section 5.1: Generic memory embeddings *)

Section GENERIC_EMBEDDING.

Definition embedding : Set := block -> option (block * Z).

Variable val_emb: embedding -> val -> val -> Prop.

Definition mem_emb (emb: embedding) (m1 m2: mem) :=
  forall ty b1 ofs v1 b2 delta,
  emb b1 = Some(b2, delta) ->
  load ty m1 b1 ofs = Some v1 ->
  exists v2, load ty m2 b2 (ofs + delta) = Some v2 /\ val_emb emb v1 v2.

Lemma valid_pointer_emb:
  forall emb m1 m2 ty b1 ofs b2 delta,
  emb b1 = Some(b2, delta) ->
  mem_emb emb m1 m2 ->
  valid_pointer ty m1 b1 ofs ->
  valid_pointer ty m2 b2 (ofs + delta).
Proof.
  intros.
  destruct (valid_pointer_load _ _ _ _ H1) as [v1 LOAD1].
  destruct (H0 _ _ _ _ _ _ H LOAD1) as [v2 [LOAD2 VEMB]].
  eapply load_valid_pointer; eauto.
Qed.

Lemma store_unmapped_emb:
  forall emb m1 m2 b ofs v ty m1',
  mem_emb emb m1 m2 ->
  emb b = None ->
  store ty m1 b ofs v = Some m1' ->
  mem_emb emb m1' m2.
Proof.
  intros; red; intros. 
  assert (load ty0 m1 b1 ofs0 = Some v1).
    rewrite <- H3. symmetry. eapply load_store_disjoint; eauto. 
    left. congruence.
  eapply H; eauto. 
Qed.

Lemma store_outside_emb:
  forall emb m1 m2 ty b ofs v m2',
  mem_emb emb m1 m2 ->
  (forall b' delta,
     emb b' = Some(b, delta) ->
     snd(bounds m1 b') + delta <= ofs \/ ofs + sizeof ty <= fst(bounds m1 b') + delta) ->
  store ty m2 b ofs v = Some m2' ->
  mem_emb emb m1 m2'.
Proof.
  intros; red; intros.
  destruct (H _ _ _ _ _ _ H2 H3) as [v2 [LOAD2 VEMB]]. 
  exists v2; split.
  rewrite <- LOAD2. eapply load_store_disjoint; eauto. 
  destruct (eq_block b2 b). 
  subst b2. generalize (H0 _ _ H2); intro. 
  destruct (load_valid_pointer _ _ _ _ _ H3) as [A [B [C D]]].
  right. omega. 
  auto.
  auto.
Qed.

Definition embedding_no_overlap (emb: embedding) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2,
  b1 <> b2 ->
  emb b1 = Some (b1', delta1) ->
  emb b2 = Some (b2', delta2) ->
  b1' <> b2' 
  \/ fst(bounds m b1) >= snd(bounds m b1)
  \/ fst(bounds m b2) >= snd(bounds m b2)
  \/ snd(bounds m b1) + delta1 <= fst(bounds m b2) + delta2 
  \/ snd(bounds m b2) + delta2 <= fst(bounds m b1) + delta1.

Lemma store_mapped_emb:
  forall emb m1 m2 b1 ofs b2 delta v1 v2 ty m1',
  mem_emb emb m1 m2 ->
  embedding_no_overlap emb m1 ->
  val_emb emb vundef vundef ->
  emb b1 = Some(b2, delta) ->
  store ty m1 b1 ofs v1 = Some m1' ->
  (forall ty', compat ty ty' ->
    val_emb emb (convert ty' v1) (convert ty' v2)) ->
  exists m2',
  store ty m2 b2 (ofs + delta) v2 = Some m2' /\ mem_emb emb m1' m2'.
Proof.
  intros.
  assert (valid_pointer ty m1 b1 ofs).
    eapply store_valid_pointer; eauto. 
  assert (valid_pointer ty m2 b2 (ofs + delta)).
    eapply valid_pointer_emb; eauto.
  destruct (valid_pointer_store _ _ _ _ v2 H6) as [m2' STORE2].
  exists m2'; split. auto.
  red. intros ty' b1' ofs' v b2' delta' CP LOAD1.
  assert (valid_pointer ty' m1 b1' ofs').
    rewrite <- (store_valid_pointer_inv _ _ _ _ _ _ ty' b1' ofs' H3). 
    eapply load_valid_pointer; eauto.
  generalize (load_store_characterization _ _ _ _ _ _ _ _ _ H3 H7).
  destruct (load_store_classification ty b1 ofs ty' b1' ofs');
  intro.
  (* similar *)
  subst b1' ofs'.
  rewrite CP in H2. inversion H2. subst b2' delta'. 
  rewrite LOAD1 in H8. inversion H8. subst v. 
  exists (convert ty' v2). split.
  eapply load_store_same; eauto.
  auto.
  (* disjoint *)
  rewrite LOAD1 in H8. 
  destruct (H _ _ _ _ _ _ CP (sym_equal H8)) as [v2' [LOAD2 VCP]].
  exists v2'. split; auto.
  rewrite <- LOAD2. eapply load_store_disjoint; eauto.
  destruct (eq_block b1 b1'). subst b1'.
  rewrite CP in H2; inversion H2.  
  right. elim o; [congruence | omega].
  assert (valid_pointer ty m1 b1 ofs).
    eapply store_valid_pointer; eauto.
  generalize (H0 _ _ _ _ _ _ n H2 CP). intros [A | [A | [A | A]]].
  left. apply sym_not_equal; auto.
  destruct H9 as [B [C [D E]]].
  generalize (sizeof_pos ty); intro. elimtype False. omega.
  destruct H7 as [B [C [D E]]]. 
  generalize (sizeof_pos ty'); intro. elimtype False. omega.
  destruct H9 as [B [C [D E]]]. destruct H7 as [U [V [W X]]]. 
  right. omega. 
  (* overlapping *)
  subst b1'. rewrite CP in H2; inversion H2; subst. 
  assert (exists v2', load ty' m2' b2 (ofs' + delta) = Some v2').
    apply valid_pointer_load.
    rewrite (store_valid_pointer_inv _ _ _ _ _ _ ty' b2 (ofs' + delta) STORE2).  
    eapply valid_pointer_emb. eexact CP. eauto.
    rewrite <- (store_valid_pointer_inv _ _ _ _ _ _ ty' b1 ofs' H3). 
    eapply load_valid_pointer; eauto.
  destruct H9 as [v2' LOAD2'].
  assert (v2' = vundef). eapply load_store_overlap; eauto. 
    omega. omega. omega.
  exists v2'; split. auto. 
  replace v with vundef by congruence. subst v2'. auto.
  (* mismatch *)
  subst b1' ofs'. rewrite CP in H2; inversion H2; subst.
  assert (exists v2', load ty' m2' b2 (ofs + delta) = Some v2').
    apply valid_pointer_load.
    rewrite (store_valid_pointer_inv _ _ _ _ _ _ ty' b2 (ofs + delta) STORE2).  
    eapply valid_pointer_emb. eexact CP. eauto.
    rewrite <- (store_valid_pointer_inv _ _ _ _ _ _ ty' b1 ofs H3). 
    eapply load_valid_pointer; eauto.
  destruct H9 as [v2' LOAD2'].
  assert (v2' = vundef). eapply load_store_mismatch; eauto. 
  exists v2'; split. auto. 
  replace v with vundef by congruence. subst v2'. auto.
Qed.

Remark alignment_shift:
  forall ty ofs delta,
  (alignof ty | ofs) -> (max_alignment | delta) ->
  (alignof ty | ofs + delta).
Proof.
  (* assert (forall a b c, (a|b) -> (b|c) -> (a|c)). *)
  (* intros. inv H; inv H0. exists (q0 * q); ring. *)
  (* intros. apply Zdivide_plus_r. auto.  *)
  (* apply H with max_alignment. apply alignof_div. auto. *)
admit.
Qed.

Lemma alloc_parallel_emb:
  forall emb m1 m2 lo1 hi1 m1' b1 lo2 hi2 m2' b2 delta,
  mem_emb emb m1 m2 ->
  alloc m1 lo1 hi1 = Some(b1, m1') ->
  alloc m2 lo2 hi2 = Some(b2, m2') ->
  emb b1 = Some(b2, delta) ->
  lo2 <= lo1 + delta -> hi1 + delta <= hi2 ->
  (max_alignment | delta) ->
  val_emb emb vundef vundef ->
  mem_emb emb m1' m2'.
Proof.
  intros; red. intros ty b ofs v b' delta'. intros.
  assert (valid_pointer ty m1' b ofs). eapply load_valid_pointer; eauto.
  destruct H9 as [A [B [C D]]].  
  destruct (eq_block b1 b).
  subst b. 
  assert (v = vundef). eapply load_alloc_same with (m := m1); eauto. subst v.
  rewrite H2 in H7; inv H7.
  exists vundef. split.
  eapply load_alloc_same_2; eauto.
  apply alignment_shift; auto.
  rewrite (alloc_result_bounds _ _ _ _ _ H0) in C. simpl in C. omega.
  rewrite (alloc_result_bounds _ _ _ _ _ H0) in D. simpl in D. omega.
  auto.
  assert (load ty m1 b ofs = Some v). 
    rewrite <- H8. symmetry. eapply load_alloc_other; eauto. 
  destruct (H _ _ _ _ _ _ H7 H9) as [v2 [LOAD2 VEMB]].
  exists v2; split.
  eapply load_alloc_other_2; eauto. 
  auto.
Qed.

Lemma alloc_right_emb:
  forall emb m1 m2 lo hi b2 m2',
  mem_emb emb m1 m2 ->
  alloc m2 lo hi = Some(b2, m2') ->
  mem_emb emb m1 m2'.
Proof.
  intros; red; intros.
  destruct (H _ _ _ _ _ _ H1 H2) as [v2 [LOAD2 VEMB]].
  exists v2; split.
  eapply load_alloc_other_2; eauto.
  auto.
Qed.

Lemma alloc_left_unmapped_emb:
  forall emb m1 m2 lo hi b1 m1',
  mem_emb emb m1 m2 ->
  alloc m1 lo hi = Some(b1, m1') ->
  emb b1 = None ->
  mem_emb emb m1' m2.
Proof.
  intros; red; intros. 
  destruct (eq_block b1 b0).
  subst b0. congruence.
  red in H. eapply H; eauto. 
  rewrite <- H3. symmetry. eapply load_alloc_other; eauto. 
Qed.

Lemma alloc_left_mapped_emb:
  forall emb m1 m2 lo hi b1 m1' b2 delta,
  mem_emb emb m1 m2 ->
  alloc m1 lo hi = Some(b1, m1') ->
  emb b1 = Some(b2, delta) ->
  valid_block m2 b2 ->
  fst(bounds m2 b2) <= lo + delta -> hi + delta <= snd(bounds m2 b2) ->
  (max_alignment | delta) ->
  (forall v, val_emb emb vundef v) ->
  mem_emb emb m1' m2.
Proof.
  intros; red; intros. 
  destruct (eq_block b1 b0).
  subst b0. rewrite H1 in H7; inv H7.
  assert (v1 = vundef). eapply load_alloc_same; eauto. subst v1.
  assert (valid_pointer ty m1' b1 ofs). eapply load_valid_pointer; eauto.
  destruct H7 as [A [B [C D]]].
  assert (valid_pointer ty m2 b3 (ofs + delta0)).
    split. auto. 
    split. apply alignment_shift; auto.
    split. rewrite (alloc_result_bounds _ _ _ _ _ H0) in C; simpl in C. omega.
    rewrite (alloc_result_bounds _ _ _ _ _ H0) in D; simpl in D. omega.
  destruct (valid_pointer_load _ _ _ _ H7) as [v2 LOAD2].
  exists v2; split. auto. auto.
  red in H. eapply H; eauto. 
  rewrite <- H8. symmetry. eapply load_alloc_other; eauto.
Qed.

Lemma free_left_emb:
  forall emb m1 m2 b1 m1',
  mem_emb emb m1 m2 ->
  free m1 b1 = Some m1' ->
  mem_emb emb m1' m2.
Proof.
  intros; red; intros.
  destruct (eq_block b0 b1).
  subst b0. elim (free_not_valid_pointer _ _ _ H0 ty ofs).
  eapply load_valid_pointer; eauto.
  red in H; eapply H; eauto.
  rewrite <- H2. symmetry. eapply load_free_other; eauto.
Qed.

Lemma free_right_emb:
  forall emb m1 m2 b2 m2',
  mem_emb emb m1 m2 ->
  (forall b1 delta,
   emb b1 = Some(b2, delta) -> ~(valid_block m1 b1)) ->
  free m2 b2 = Some m2' ->
  mem_emb emb m1 m2'.
Proof.
  intros; red; intros.
  destruct (H _ _ _ _ _ _ H2 H3) as [v2 [LOAD2 VEMB]].
  exists v2; split.
  rewrite <- LOAD2. eapply load_free_other; eauto. 
  red; intro; subst b0. 
  elim (H0 b1 delta); auto.
  generalize (load_valid_pointer _ _ _ _ _ H3). intro. inv H4; auto.
  auto.
Qed.

Fixpoint free_list (m: mem) (bl: list block) {struct bl} : option mem :=
  match bl with
  | nil => Some m
  | b :: bs =>
      match free_list m bs with
      | None => None
      | Some m1 => free m1 b
      end
  end.

Lemma free_list_left_emb:
  forall emb m2 l m1 m1',
  mem_emb emb m1 m2 ->
  free_list m1 l = Some m1' ->
  mem_emb emb m1' m2.
Proof.
  induction l; simpl.
  intros; inv H0; auto.
  intros m1 m1' EMB. case_eq (free_list m1 l). 2:congruence. intros.
  apply free_left_emb with m a; eauto.
Qed.

Remark free_list_not_valid_block:
  forall m bl m',
  free_list m bl = Some m' ->
  forall b, In b bl -> ~(valid_block m' b).
Proof.
  induction bl; simpl.
  intros. contradiction.
  intro m'. case_eq (free_list m bl). 2: congruence. intros.
  destruct (eq_block b a). 
  subst b. eapply free_not_valid_block; eauto.
  rewrite (free_valid_block _ _ _ b H0 n).
  eapply IHbl; eauto. intuition congruence.
Qed.

Lemma free_list_free_parallel_emb:
  forall emb m1 m2 bl b2 m1' m2',
  mem_emb emb m1 m2 ->
  free_list m1 bl = Some m1' ->
  free m2 b2 = Some m2' ->
  (forall b delta', emb b = Some(b2, delta') -> In b bl) ->
  mem_emb emb m1' m2'.
Proof.
  intros. eapply free_right_emb; eauto. 
  eapply free_list_left_emb; eauto. 
  intros. eapply free_list_not_valid_block; eauto. 
Qed.

Lemma free_parallel_emb:
  forall emb m1 m2 b1 b2 m1' m2',
  mem_emb emb m1 m2 ->
  free m1 b1 = Some m1' ->
  free m2 b2 = Some m2' ->
  (forall b delta', emb b = Some(b2, delta') -> b = b1) ->
  mem_emb emb m1' m2'.
Proof.
  intros. 
  eapply free_right_emb; eauto. 
  eapply free_left_emb; eauto.
  intros. assert (b0 = b1) by eauto. subst b0.  
  eapply free_not_valid_block; eauto.
Qed.

End GENERIC_EMBEDDING.

(** ** Section 5.2: Memory extensions *)

Section MEM_EXTENDS.

Definition emb_id : embedding := fun b => Some(b, 0).

Definition val_emb_id (emb: embedding) (v1 v2: val) := v1 = v2.

Definition mem_extends (m1 m2: mem) :=
  same_domain m1 m2 /\ mem_emb val_emb_id emb_id m1 m2.

Lemma mem_extends_refl:
  forall m, mem_extends m m.
Proof.
  intros. split. red; intros; tauto. 
  red; intros. exists v1; split. 
  unfold emb_id in H. inv H. replace (ofs + 0) with ofs by omega. auto.
  red; auto.
Qed.

Lemma mem_extends_trans:
  forall m1 m2 m3, mem_extends m1 m2 -> mem_extends m2 m3 -> mem_extends m1 m3.
Proof.
  intros. destruct H; destruct H0. split.
  red; intros. rewrite (H b). apply H0.
  red; intros. destruct (H1 _ _ _ _ _ _ H3 H4) as [v2 [LOAD2 VEMB2]].
  generalize H3. unfold emb_id; intro EQ; inv EQ.
  replace (ofs + 0) with ofs in LOAD2 by omega.
  destruct (H2 _ _ _ _ _ _ H3 LOAD2) as [v3 [LOAD3 VEMB3]].
  exists v3; split. auto. 
  red. transitivity v2. auto. auto.
Qed.

Lemma alloc_extends:
  forall m1 m2 lo1 hi1 b1 m1' lo2 hi2 b2 m2',
  mem_extends m1 m2 ->
  alloc m1 lo1 hi1 = Some(b1, m1') ->
  alloc m2 lo2 hi2 = Some(b2, m2') ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  b1 = b2 /\ mem_extends m1' m2'.
Proof.
  intros. destruct H. 
  assert (b1 = b2 /\ same_domain m1' m2'). 
    eapply alloc_same_domain; eauto. 
  destruct H5. subst b2. split. auto. split. auto.
  eapply alloc_parallel_emb; eauto. 
  unfold emb_id; reflexivity. omega. omega. 
  apply Zdivide_0.
  red; auto.
Qed.

Lemma load_extends:
  forall m1 m2 ty b ofs v,
  mem_extends m1 m2 ->
  load ty m1 b ofs = Some v ->
  load ty m2 b ofs = Some v.
Proof.
  intros. destruct H. 
  assert (emb_id b = Some(b, 0)). unfold emb_id; auto.
  destruct (H1 _ _ _ _ _ _ H2 H0) as [v2 [LOAD VEMB]].
  red in VEMB. replace ofs with (ofs + 0) by omega. congruence.
Qed.

Lemma store_within_extends:
  forall m1 m2 ty b ofs v m1',
  mem_extends m1 m2 ->
  store ty m1 b ofs v = Some m1' ->
  exists m2', store ty m2 b ofs v = Some m2' /\ mem_extends m1' m2'.
Proof.
  intros. destruct H.
  assert (exists m2', store ty m2 b (ofs + 0) v = Some m2' /\ mem_emb val_emb_id emb_id m1' m2').
    eapply store_mapped_emb; eauto.
    red; unfold emb_id; intros. inv H3. inv H4. auto.
    red; auto.
    reflexivity.
    intros; red; auto.
  destruct H2 as [m2' [STORE MEMB]]. 
  replace (ofs + 0) with ofs in STORE by omega.
  exists m2'; split. auto. split. eapply store_same_domain; eauto. auto.
Qed.
 
Lemma store_outside_extends:
  forall m1 m2 ty b ofs v m2',
  mem_extends m1 m2 ->
  ofs + sizeof ty <= fst(bounds m1 b) \/ snd(bounds m1 b) <= ofs ->
  store ty m2 b ofs v = Some m2' ->
  mem_extends m1 m2'.
Proof.
  intros. destruct H.
  split. red; intros. rewrite (store_fresh_block _ _ _ _ _ _ b0 H1). auto.
  eapply store_outside_emb; eauto. 
  unfold emb_id; intros. inv H3. omega. 
Qed.

Lemma free_extends:
  forall m1 m2 b m1' m2',
  mem_extends m1 m2 ->
  free m1 b = Some m1' ->
  free m2 b = Some m2' ->
  mem_extends m1' m2'.
Proof.
  intros. destruct H. split. 
  eapply free_same_domain; eauto. 
  eapply free_parallel_emb; eauto. 
  unfold emb_id; intros. congruence.
Qed.

End MEM_EXTENDS.

(** ** Section 5.3: Refinement of stored values *)

Section MEM_LESSDEF.

Definition val_lessdef (v1 v2: val) := v1 = vundef \/ v1 = v2.

Definition val_emb_lessdef (emb: embedding) (v1 v2: val) :=
  val_lessdef v1 v2.

Definition mem_lessdef (m1 m2: mem) :=
  same_domain m1 m2 /\ mem_emb val_emb_lessdef emb_id m1 m2.

Lemma mem_lessdef_refl:
  forall m, mem_lessdef m m.
Proof.
  intros. split. red; intros; tauto. 
  red; intros. exists v1; split. 
  unfold emb_id in H. inv H. replace (ofs + 0) with ofs by omega. auto.
  hnf; auto.
Qed.

Lemma mem_lessdef_trans:
  forall m1 m2 m3, mem_lessdef m1 m2 -> mem_lessdef m2 m3 -> mem_lessdef m1 m3.
Proof.
  intros. destruct H; destruct H0. split.
  red; intros. rewrite (H b). apply H0.
  red; intros. destruct (H1 _ _ _ _ _ _ H3 H4) as [v2 [LOAD2 VEMB2]].
  generalize H3. unfold emb_id; intro EQ; inv EQ.
  replace (ofs + 0) with ofs in LOAD2 by omega.
  destruct (H2 _ _ _ _ _ _ H3 LOAD2) as [v3 [LOAD3 VEMB3]].
  exists v3; split. auto. 
  hnf. hnf in VEMB2. hnf in VEMB3. intuition congruence.
Qed.

Lemma alloc_lessdef:
  forall m1 m2 lo1 hi1 b1 m1' lo2 hi2 b2 m2',
  mem_lessdef m1 m2 ->
  alloc m1 lo1 hi1 = Some(b1, m1') ->
  alloc m2 lo2 hi2 = Some(b2, m2') ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  b1 = b2 /\ mem_lessdef m1' m2'.
Proof.
  intros. destruct H. 
  assert (b1 = b2 /\ same_domain m1' m2'). 
    eapply alloc_same_domain; eauto. 
  destruct H5. subst b2. split. auto. split. auto.
  eapply alloc_parallel_emb; eauto. 
  unfold emb_id; reflexivity. omega. omega. 
  apply Zdivide_0.
  hnf; auto.
Qed.

Lemma load_lessdef:
  forall m1 m2 ty b ofs v1,
  mem_lessdef m1 m2 ->
  load ty m1 b ofs = Some v1 ->
  exists v2, load ty m2 b ofs = Some v2 /\ val_lessdef v1 v2.
Proof.
  intros. destruct H.
  replace ofs with (ofs + 0) by omega.
  apply (H1 ty b ofs v1); auto.
Qed.

Hypothesis convert_monotone:
  forall ty v1 v2, val_lessdef v1 v2 -> val_lessdef (convert ty v1) (convert ty v2).

Lemma store_lessdef:
  forall m1 m2 ty b ofs v1 m1' v2,
  mem_lessdef m1 m2 ->
  store ty m1 b ofs v1 = Some m1' ->
  val_lessdef v1 v2 ->
  exists m2', store ty m2 b ofs v2 = Some m2' /\ mem_lessdef m1' m2'.
Proof.
  intros. destruct H.
  assert (exists m2', store ty m2 b (ofs + 0) v2 = Some m2' /\ mem_emb val_emb_lessdef emb_id m1' m2').
    eapply store_mapped_emb; eauto.
    red; unfold emb_id; intros. inv H4. inv H5. auto.
    red; auto.
    red; auto. 
    reflexivity.
    intros. red. apply convert_monotone; auto.
  destruct H3 as [m2' [STORE MEMB]]. 
  replace (ofs + 0) with ofs in STORE by omega.
  exists m2'; split. auto. split. eapply store_same_domain; eauto. auto.
Qed.

Lemma free_lessdef:
  forall m1 m2 b m1' m2',
  mem_lessdef m1 m2 ->
  free m1 b = Some m1' ->
  free m2 b = Some m2' ->
  mem_lessdef m1' m2'.
Proof.
  intros. destruct H. split. 
  eapply free_same_domain; eauto. 
  eapply free_parallel_emb; eauto. 
  unfold emb_id; intros. congruence.
Qed.

End MEM_LESSDEF.

(** ** Section 5.4: Memory injections *)

Section MEM_INJECT.

Variable val_inject: embedding -> val -> val -> Prop.

Record mem_inject (f: embedding) (m1 m2: mem) : Prop :=
  mk_mem_inject {
    mi_emb:
      mem_emb val_inject f m1 m2;
    mi_freeblocks:
      forall b, fresh_block m1 b -> f b = None;
    mi_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> ~(fresh_block m2 b');
    mi_no_overlap:
      embedding_no_overlap f m1
  }.

Lemma load_inject:
  forall emb m1 m2 ty b1 ofs v1 b2 delta,
  mem_inject emb m1 m2 ->
  load ty m1 b1 ofs = Some v1 ->
  emb b1 = Some(b2, delta) ->
  exists v2, load ty m2 b2 (ofs + delta) = Some v2 /\ val_inject emb v1 v2.
Proof.
  intros. destruct H. apply (mi_emb0 ty b1 ofs v1); auto.
Qed.

Hypothesis val_inject_undef:
  forall emb v, val_inject emb vundef v.

Hypothesis convert_inject:
  forall emb ty v1 v2,
  val_inject emb v1 v2 -> 
  val_inject emb (convert ty v1) (convert ty v2).

Lemma store_mapped_inject:
  forall emb m1 m2 ty b1 ofs v1 m1' b2 delta v2,
  mem_inject emb m1 m2 ->
  store ty m1 b1 ofs v1 = Some m1' ->
  val_inject emb v1 v2 ->
  emb b1 = Some(b2, delta) ->
  exists m2', store ty m2 b2 (ofs + delta) v2 = Some m2' /\ mem_inject emb m1' m2'.
Proof.
  intros. destruct H.
  assert (exists m2', store ty m2 b2 (ofs + delta) v2 = Some m2' /\ mem_emb val_inject emb m1' m2').
    eapply store_mapped_emb; eauto.
  destruct H as [m2' [STORE MEMB]].
  exists m2'; split. auto. 
  constructor.
  (* embedding *)
  auto.
  (* freeblocks *)
  intros. rewrite (store_fresh_block _ _ _ _ _ _ b H0) in H. auto.
  (* mappedblocks *)
  intros. rewrite (store_fresh_block _ _ _ _ _ _ b' STORE). eauto.
  (* overlap *)
  red; intros. 
  rewrite (store_bounds_inv _ _ _ _ _ _ b0 H0).  
  rewrite (store_bounds_inv _ _ _ _ _ _ b3 H0).
  auto.
Qed.

Lemma store_unmapped_inject:
  forall emb m1 m2 ty b1 ofs v1 m1',
  mem_inject emb m1 m2 ->
  store ty m1 b1 ofs v1 = Some m1' ->
  emb b1 = None ->
  mem_inject emb m1' m2.
Proof.
  intros. destruct H. 
  constructor.
  (* embedding *)
  eapply store_unmapped_emb; eauto. 
  (* freeblocks *)
  intros. rewrite (store_fresh_block _ _ _ _ _ _ b H0) in H. auto.
  (* mappedblocks *)
  auto.
  (* overlap *)
  red; intros. 
  rewrite (store_bounds_inv _ _ _ _ _ _ b0 H0).  
  rewrite (store_bounds_inv _ _ _ _ _ _ b2 H0).
  auto.
Qed.

Section LOADV.

Variable proj_pointer: val -> option (block * Z).

Hypothesis val_inject_proj_pointer:
  forall v1 v2 b1 ofs1 emb,
  proj_pointer v1 = Some(b1, ofs1) ->
  val_inject emb v1 v2 ->
  exists b2, exists ofs2, exists delta,
  proj_pointer v2 = Some(b2, ofs2) /\
  emb b1 = Some(b2, delta) /\
  ofs2 = ofs1 + delta.

Lemma loadv_inject:
  forall ty m1 addr1 v1 emb addr2 m2,
  loadv proj_pointer ty m1 addr1 = Some v1 ->
  val_inject emb addr1 addr2 ->
  mem_inject emb m1 m2 ->
  exists v2, loadv proj_pointer ty m2 addr2 = Some v2 /\ val_inject emb v1 v2.
Proof.
  intros until m2. unfold loadv. case_eq (proj_pointer addr1). 2: congruence.
  intros [b1 ofs1]. intros. 
  destruct (val_inject_proj_pointer _ _ _ _ _ H H1) as [b2 [ofs2 [delta [A [B C]]]]].
  rewrite A. rewrite C. eapply load_inject; eauto. 
Qed.

Lemma storev_inject:
  forall ty m1 addr1 v1 m1' emb addr2 v2 m2,
  storev proj_pointer ty m1 addr1 v1 = Some m1' ->
  val_inject emb addr1 addr2 ->
  val_inject emb v1 v2 ->
  mem_inject emb m1 m2 ->
  exists m2', storev proj_pointer ty m2 addr2 v2 = Some m2' /\ mem_inject emb m1' m2'.
Proof.
  intros until m2. unfold storev. case_eq (proj_pointer addr1). 2: congruence.
  intros [b1 ofs1]. intros. 
  destruct (val_inject_proj_pointer _ _ _ _ _ H H1) as [b2 [ofs2 [delta [A [B C]]]]].
  rewrite A. rewrite C. eapply store_mapped_inject; eauto. 
Qed.

End LOADV.

Lemma embedding_no_overlap_free:
  forall emb m b m',
  free m b = Some m' ->
  embedding_no_overlap emb m ->
  embedding_no_overlap emb m'.
Proof.
  intros; red; intros.
  assert (fst (bounds m' b) >= snd (bounds m' b)).
    rewrite (free_same_bounds _ _ _ H). omega.
  destruct (eq_block b1 b); destruct (eq_block b2 b); subst; auto.
  rewrite (free_bounds_inv _ _ _ _ H n).
  rewrite (free_bounds_inv _ _ _ _ H n0).
  auto.
Qed.

Lemma embedding_no_overlap_free_list:
  forall emb m bl m',
  free_list m bl = Some m' ->
  embedding_no_overlap emb m ->
  embedding_no_overlap emb m'.
Proof.
  induction bl; simpl; intros.
  inv H; auto.
  generalize H; clear H. case_eq (free_list m bl). 
  intros m1 F1 F2. eapply embedding_no_overlap_free; eauto. 
  congruence.
Qed.

Remark free_list_fresh_block:
  forall m l m' b,
  free_list m l = Some m' ->
  (fresh_block m' b <-> fresh_block m b).
Proof.
  induction l; simpl.
  intros. inv H. tauto.
  case_eq (free_list m l); intros. 2: congruence.
  rewrite (free_fresh_block _ _ _ b H0).
  eapply IHl; eauto. 
Qed.

Lemma free_inject:
  forall emb m1 m2 l b m1' m2',
  (forall b1 delta, emb b1 = Some(b, delta) -> In b1 l) ->
  free_list m1 l = Some m1' ->
  free m2 b = Some m2' ->
  mem_inject emb m1 m2 ->
  mem_inject emb m1' m2'.
Proof.
  intros. inv H2. constructor.
  (* embedding *)
  eapply free_list_free_parallel_emb; eauto. 
  (* freeblocks *)
  intros. apply mi_freeblocks0. 
  rewrite <- (free_list_fresh_block _ _ _ b0 H0). auto. 
  (* mapped blocks *)
  intros. rewrite (free_fresh_block _ _ _ b' H1). eauto. 
  (* no overlap *)
  eapply embedding_no_overlap_free_list; eauto.
Qed.

Definition embedding_incr (emb1 emb2: embedding) : Prop :=
  forall b, emb2 b = emb1 b \/ emb1 b = None.

Hypothesis val_inject_incr:
  forall emb1 emb2 v1 v2,
  embedding_incr emb1 emb2 ->
  val_inject emb1 v1 v2 ->
  val_inject emb2 v1 v2.

Definition extend_embedding (b: block) (x: option (block * Z))
                            (emb: embedding): embedding :=
  fun (b': block) => if eq_block b' b then x else emb b'.

Lemma extend_embedding_incr:
  forall emb b x,
  emb b = None -> embedding_incr emb (extend_embedding b x emb).
Proof.
  intros; red; intros. unfold extend_embedding.
  destruct (eq_block b0 b). subst b0; auto. auto.
Qed.

Lemma alloc_right_inject:
  forall emb m1 m2 lo hi b2 m2',
  mem_inject emb m1 m2 ->
  alloc m2 lo hi = Some(b2, m2') ->
  mem_inject emb m1 m2'.
Proof.
  intros. inv H. constructor.
  (* embedding *)
  eapply alloc_right_emb; eauto.
  (* fresh *)
  auto.
  (* valid *)
  intros. rewrite (alloc_fresh_block _ _ _ _ _ b' H0).
  generalize (mi_mappedblocks0 _ _ _ H). tauto. 
  (* no overlap *)
  auto.
Qed.

Lemma alloc_left_unmapped_inject:
  forall emb m1 m2 lo hi b1 m1',  
  mem_inject emb m1 m2 ->
  alloc m1 lo hi = Some(b1, m1') ->
  mem_inject (extend_embedding b1 None emb) m1' m2
  /\ embedding_incr emb (extend_embedding b1 None emb).
Proof.
  intros. inv H.
  assert (INCR: embedding_incr emb (extend_embedding b1 None emb)).
    red. intro. unfold extend_embedding. destruct (eq_block b b1).
    subst b1. right. apply mi_freeblocks0. 
    eapply alloc_fresh_block_2; eauto.
    auto.
 split; auto. constructor.
  (* embedding *)
  eapply alloc_left_unmapped_emb; eauto.
  red; intros. unfold extend_embedding in H.
  destruct (eq_block b0 b1). discriminate. 
  destruct (mi_emb0 _ _ _ _ _ _ H H1) as [v2 [A B]]. 
  exists v2; split. auto. eapply val_inject_incr; eauto.
  unfold extend_embedding. destruct (eq_block b1 b1); congruence.
  (* fresh *)
  intros. unfold extend_embedding. destruct (eq_block b b1). auto.
  apply mi_freeblocks0. 
  generalize (alloc_fresh_block _ _ _ _ _ b H0). tauto.
  (* mapped *)
  unfold extend_embedding. intros. destruct (eq_block b b1).
  discriminate. eauto.
  (* overlap *)
  unfold extend_embedding; red; intros.
  destruct (eq_block b0 b1). discriminate.
  destruct (eq_block b2 b1). discriminate.
  rewrite (alloc_bounds_inv _ _ _ _ _ _ H0 n). 
  rewrite (alloc_bounds_inv _ _ _ _ _ _ H0 n0).
  apply mi_no_overlap0; auto.
Qed.

Lemma alloc_left_mapped_inject:
  forall emb m1 m2 lo hi b1 m1' b2 ofs, 
  mem_inject emb m1 m2 ->
  alloc m1 lo hi = Some(b1, m1') ->
  valid_block m2 b2 ->
  fst (bounds m2 b2) <= lo + ofs ->
  hi + ofs <= snd(bounds m2 b2) ->
  (max_alignment | ofs) ->
  (forall b' ofs',
     emb b' = Some(b2, ofs') ->
     snd (bounds m1 b') + ofs' <= lo + ofs \/
     hi + ofs <= fst (bounds m1 b') + ofs') ->
  mem_inject (extend_embedding b1 (Some(b2, ofs)) emb) m1' m2
  /\ embedding_incr emb (extend_embedding b1 (Some(b2, ofs)) emb).
Proof.
  intros. inv H.
  assert (INCR: embedding_incr emb (extend_embedding b1 (Some(b2, ofs)) emb)).
    red. intro. unfold extend_embedding. destruct (eq_block b b1).
    subst b1. right. apply mi_freeblocks0. eapply alloc_fresh_block_2; eauto.
    auto.
 split; auto. constructor.
  (* embedding *)
  eapply alloc_left_mapped_emb; eauto.
  red; intros. unfold extend_embedding in H.
  destruct (eq_block b0 b1). subst b0.
  destruct (load_valid_pointer _ _ _ _ _ H6) as [A [B [C D]]].
  elim (alloc_not_valid_block _ _ _ _ _ H0 A). 
  destruct (mi_emb0 _ _ _ _ _ _ H H6) as [v2 [A B]]. 
  exists v2; split. auto. eapply val_inject_incr; eauto.
  unfold extend_embedding. destruct (eq_block b1 b1); congruence.
  (* fresh *)
  intros. unfold extend_embedding. destruct (eq_block b b1).
  subst b. rewrite (alloc_fresh_block _ _ _ _ _ b1 H0) in H.
  intuition congruence.
  apply mi_freeblocks0.
  generalize (alloc_fresh_block _ _ _ _ _ b H0). tauto.
  (* mapped *)
  unfold extend_embedding. intros. destruct (eq_block b b1).
  inv H. red; intro. eapply fresh_valid_block_exclusive; eauto. 
  eauto.
  (* overlap *)
  unfold extend_embedding; red; intros.
  assert (forall b, bounds m1' b = if eq_block b b1 then (lo, hi) else bounds m1 b).
    intros. destruct (eq_block b b1).
    subst b. eapply alloc_result_bounds; eauto.
    eapply alloc_bounds_inv; eauto.
  repeat rewrite H8. clear H8.
  destruct (eq_block b0 b1); destruct (eq_block b3 b1); simpl.
  subst b0 b3. congruence.
  subst b0. injection H6; clear H6; intros; subst b1' delta1.
  destruct (eq_block b2 b2').
    right. subst b2'. generalize (H5 _ _ H7). omega.
    left. auto.
  subst b3. injection H7; clear H7; intros; subst b2' delta2.  
  destruct (eq_block b1' b2).
    right. subst b1'. generalize (H5 _ _ H6). omega.
    left. auto.
  eapply mi_no_overlap0; eauto.
Qed.

Fixpoint alloc_list (m: mem) (req: list (Z * Z)) {struct req} : option (list block * mem) :=
  match req with
  | nil => Some(nil, m)
  | (lo, hi) :: req' =>
      match alloc m lo hi with
      | None => None
      | Some(b1, m1) =>
          match alloc_list m1 req' with
          | None => None
          | Some(bl, m2) => Some(b1 :: bl, m2)
          end
      end
  end.

Inductive list_forall2 (A B: Set) (P: A -> B -> Prop): list A -> list B -> Prop :=
  | list_forall2_nil:
      list_forall2 A B P nil nil
  | list_forall2_cons: forall hd1 tl1 hd2 tl2,
      P hd1 hd2 -> list_forall2 A B P tl1 tl2 ->
      list_forall2 A B P (hd1 :: tl1) (hd2 :: tl2).

Implicit Arguments list_forall2 [A B].

Inductive disjoint_req (lo hi: Z): list (Z*Z) -> list(option Z) -> Prop :=
  | disjoint_req_nil:
      disjoint_req lo hi nil nil
  | disjoint_req_cons: forall lo' hi' optdelta req map,
      match optdelta with
      | None => True
      | Some delta => hi' + delta <= lo \/ hi <= lo' + delta 
      end ->
      disjoint_req lo hi req map ->
      disjoint_req lo hi ((lo', hi') :: req) (optdelta :: map).

Inductive wf_req (lob hib: Z): list (Z*Z) -> list(option Z) -> Prop :=
  | wf_req_nil:
      wf_req lob hib nil nil
  | wf_req_cons: forall lo hi optdelta req map,
      match optdelta with
      | None => True
      | Some delta =>
          lob <= lo + delta /\ hi + delta <= hib /\
          (max_alignment | delta) /\
          disjoint_req (lo + delta) (hi + delta) req map
      end ->
      wf_req lob hib req map ->
      wf_req lob hib ((lo, hi) :: req) (optdelta :: map).

Lemma alloc_list_left_inject:
  forall m2 b2, valid_block m2 b2 ->
  forall req map, wf_req (fst (bounds m2 b2)) (snd (bounds m2 b2)) req map ->
  forall emb m1 bl m1', 
  mem_inject emb m1 m2 ->
  alloc_list m1 req = Some(bl, m1') ->
  (forall b' ofs',
    emb b' = Some(b2, ofs') ->
    disjoint_req (fst(bounds m1 b') + ofs') (snd(bounds m1 b') + ofs') req map) ->
  exists emb',
  mem_inject emb' m1' m2
  /\ list_forall2
       (fun (mp: option Z) (b: block) =>
         emb' b = match mp with None => None | Some ofs => Some(b2, ofs) end)
       map bl
  /\ (forall b, ~fresh_block m1 b -> emb' b = emb b).
Proof.
  intros m2 b2 VB2. induction 1; intros until m1'; simpl.
  (* base case *)
  intros MINJ ALLOC DISJ. inversion ALLOC; clear ALLOC; subst bl m1'.
  exists emb; split. auto. split. constructor. auto.
  (* inductive case *)
  case_eq (alloc m1 lo hi). 2:congruence. intros [b1 m] ALLOC MINJ.
  case_eq (alloc_list m req). 2:congruence. intros [bl1 m1''] ALLOCLIST EQ DISJ.
  inversion EQ; clear EQ; subst bl m1''.
  pose (img := match optdelta with None => None | Some delta => Some(b2, delta) end).
  pose (emb' := extend_embedding b1 img emb).
  assert (mem_inject emb' m m2 /\ embedding_incr emb emb').
    unfold emb', img. destruct optdelta as [delta | ].
    eapply alloc_left_mapped_inject; eauto. tauto. tauto. tauto. 
    intros. generalize (DISJ _ _ H1); intro. inv H2. tauto.
    eapply alloc_left_unmapped_inject; eauto. 
  destruct H1 as [MINJ' INCR].
  assert (DISJ': forall b' ofs', emb' b' = Some(b2, ofs') ->
             disjoint_req (fst (bounds m b') + ofs') (snd (bounds m b') + ofs') req map).
    intros until ofs'. unfold emb', extend_embedding. destruct (eq_block b' b1).
    unfold img. destruct optdelta as [delta|]; intro EQ; simplify_eq EQ; clear EQ. 
    intro; subst ofs' b'.
    rewrite (alloc_result_bounds _ _ _ _ _ ALLOC). simpl. tauto.
    intros. rewrite (alloc_bounds_inv _ _ _ _ _ _ ALLOC n).
    generalize (DISJ _ _ H1); intro. inv H2; auto.
  destruct (IHwf_req _ _ _ _ MINJ' ALLOCLIST DISJ') as [emb'' [A [B C]]].
  exists emb''; split. auto. 
  split. constructor; auto. rewrite C. unfold emb', extend_embedding. 
    destruct (eq_block b1 b1). 2: congruence. reflexivity. 
    red; intro. eapply fresh_valid_block_exclusive. eauto. 
    rewrite (alloc_valid_block _ _ _ _ _ b1 ALLOC). auto.
  intros. rewrite C.  unfold emb', extend_embedding.
  destruct (eq_block b b1). subst b.
  elim H1. eapply alloc_fresh_block_2; eauto. auto.
  rewrite (alloc_fresh_block _ _ _ _ _ b ALLOC). tauto.
Qed.

Lemma alloc_list_alloc_inject:
  forall req map emb m1 m2 bl m1' b2 m2' lo hi, 
  mem_inject emb m1 m2 ->
  alloc_list m1 req = Some(bl, m1') ->
  alloc m2 lo hi = Some(b2, m2') ->
  wf_req lo hi req map ->
  exists emb',
  mem_inject emb' m1' m2'
  /\ list_forall2
       (fun (rq: option Z) (b: block) =>
         emb' b = match rq with None => None | Some delta => Some(b2, delta) end)
       map bl
  /\ embedding_incr emb emb'.
Proof.
  intros. 
  assert (VALB: valid_block m2' b2).
    rewrite (alloc_valid_block _ _ _ _ _ b2 H1). auto.
  assert (MINJ: mem_inject emb m1 m2').
    eapply alloc_right_inject; eauto.
  assert (DISJ: forall b' ofs', emb b' = Some(b2, ofs') ->
          disjoint_req (fst (bounds m1 b') + ofs') (snd (bounds m1 b') + ofs') req map).
    intros. inversion H. elim (mi_mappedblocks0 _ _ _ H3).
    eapply alloc_fresh_block_2; eauto.
  assert (WFREQ: wf_req (fst (bounds m2' b2)) (snd (bounds m2' b2)) req map).
    rewrite (alloc_result_bounds _ _ _ _ _ H1). simpl; auto.
  destruct (alloc_list_left_inject _ _ VALB _ _ WFREQ _ _ _ _ MINJ H0 DISJ)
  as [emb' [A [B C]]].
  exists emb'; split. auto. split. auto.
  red; intros. inv H. case_eq (emb b); intros.
  left. rewrite <- H. apply C. red; intro. generalize (mi_freeblocks0 _ H3); intro. congruence.
  right. auto.
Qed.

End MEM_INJECT.

End Rel_Mem.


