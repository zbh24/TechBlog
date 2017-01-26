(** * Section 3: Abstract memory model *)

Module Type GEN_MEM.

Variable block: Set.
Variable mem: Set.

Variable empty: mem.
Variable alloc: mem -> Z -> Z -> option (block * mem).
Variable load: memtype -> mem -> block -> Z -> option val.
Variable store: memtype -> mem -> block -> Z -> val -> option mem.
Variable free: mem -> block -> option mem.
Hypothesis eq_block: forall (b1 b2: block), {b1=b2} + {b1<>b2}.

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

End GEN_MEM.

(** The above is the hypothesis *)
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

End Gen_Mem_Facts.

(** * Section 4: concrete memory model *)

(** The concrete memory model is first specified by the properties it
  satisfies. *)

Module Type REF_GEN_MEM.

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

End Concrete_Mem.


(** * Section 5: Relating two memory states before and after program transformation *)

Module Rel_Mem(M: REF_GEN_MEM).

Module MF := Gen_Mem_Facts(M).
Module RMF := Ref_Gen_Mem_Facts(M).
Import M.
Import MF.
Import RMF.

Section GENERIC_EMBEDDING.

Definition embedding : Set := block -> option (block * Z).

Definition embedding : Set := fun (b:block) => option (block *z).

Variable val_emb: embedding -> val -> val -> Prop.
