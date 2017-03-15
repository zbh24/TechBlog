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

Load seplog_header.
Require Import topsy_hm.
Require Import topsy_hmAlloc.
Require Import Bool.

(***************************************************)
(* Definition and Lemmas for contiguous free block *)
(***************************************************)

Fixpoint Free_block_list (l:list nat) {struct l} : list (nat * bool) :=
  match l with
    nil => nil
    | hd::tl => (hd,true) :: Free_block_list tl
  end.

Fixpoint nat_list_sum (l:list nat) {struct l}: nat :=
  match l with
    nil => 0
    | hd::tl => hd + (nat_list_sum tl)
  end.

Definition Free_block_compact_size (l:list nat) :=
  nat_list_sum l + 2 * length l - 2.


Lemma Free_block_list_nempty: forall l,
  (Free_block_compact_size l > 0) ->
  l <> nil.
  destruct l; unfold Free_block_compact_size; simpl; intros; (discriminate || omega).
Qed.



  (* first execution of findFree: 
    i) the heap-list is the same as in the precondition of the specification of hmAlloc
    ii) either their exists a block big enough or such a block does not exist
  *)

Definition findFree_specif2 := forall adr size (*entry fnd sz stts result*),
  size > 0 ->
  adr > 0 ->
  (*    var.set (hmStart::entry::fnd::sz::stts::result::nil) ->*)

  {{fun s => fun h => exists l1, exists l2, exists l,  
    (Heap_List (l1 ++ (Free_block_list l) ++ l2) adr) s h /\
    (Free_block_compact_size l) >= size /\
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s }}

  findFree size entry fnd sz stts

  {{fun s => fun h =>  exists l1, exists l2, exists l,  
    (Heap_List (l1 ++ (Free_block_list l) ++ l2) adr) s h /\
    (Free_block_compact_size l) >= size /\
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\
    (
      (exists finded_free_block, exists size'', size'' >= size /\ 
        In_hl (l1 ++ (Free_block_list l) ++ l2) (finded_free_block,size'',free) adr /\ 
        eval (var_e entry) s = (Z_of_nat finded_free_block) /\ 
        finded_free_block > 0)
      \/
      (eval (var_e entry) s = eval null s)
    )}}.

Lemma findFree_verif2: findFree_specif2.
  unfold findFree_specif2.
  intros.

  unfold findFree.

  (* entry <- var_e hmStart; *)

  Step (

    fun (s : store.s) (h : heap.h) =>
      exists l1,
        (exists l2,
          (exists l : list nat,
            Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
            Free_block_compact_size l >= size /\
            eval (var_e hmStart) s = eval (nat_e adr) s /\
            eval (var_e result) s = eval null s /\
            eval (var_e entry) s = eval (nat_e adr) s))
  ).

  Decompose_hyp.
  red.
  exists x; exists x0; exists x1.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).

  (* stts <-* entry -.> status; *)


  Step (
    fun (s : store.s) (h : heap.h) =>
      exists l1,
        (exists l2,
          (exists l : list nat,
            Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
            Free_block_compact_size l >= size /\
            eval (var_e hmStart) s = eval (nat_e adr) s /\
            eval (var_e result) s = eval null s /\
            eval (var_e entry) s = eval (nat_e adr) s))
  ).

  Decompose_hyp.

  destruct x.
  assert (Free_block_compact_size x1 > 0).
  omega.
  generalize (Free_block_list_nempty x1 H2); intros.
  destruct x1; try tauto.
  simpl in H1.
  exists Free.
  apply cell_read.
  split.
  generalize (hl_getstatus nil (Free_block_list x1 ++ x0) n true adr s h H1); intros.
  simpl in H8.
  unfold status.
  Decompose_sepcon H8 h1 h2.
  Compose_sepcon h1 h2; [Mapsto | red; auto].
  red.
  exists (@nil (nat*bool)); exists x0; exists (n::x1).

  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).

  destruct p.
  exists (hlstat_bool2expr b).
  apply cell_read.
  split.
  generalize (hl_getstatus nil (x ++ Free_block_list x1 ++ x0) n b adr s h H1); intros.
  simpl in H2.
  unfold status.
  Decompose_sepcon H2 h1 h2.
  Compose_sepcon h1 h2; [Mapsto | red; auto].
  red.
  exists ((n,b)::x); exists x0; exists x1.

  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).

  (* fnd <- int_e 0%Z; *)

  Step (
    fun (s : store.s) (h : heap.h) =>
      exists l1,
        (exists l2,
          (exists l : list nat,
            Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
            Free_block_compact_size l >= size /\
            eval (var_e hmStart) s = eval (nat_e adr) s /\
            eval (var_e result) s = eval null s /\
            eval (var_e entry) s = eval (nat_e adr) s /\
            eval (var_e fnd) s = eval (nat_e 0) s
          ))
  ).

  red.
  Decompose_hyp. 
  exists x; exists x0; exists x1.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).

  (* while ((var_e entry =/= null) &&& (var_e fnd =/= int_e 1%Z)) invariant *)


  Step (fun s h => exists l1, exists l2, exists l,
    Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
    Free_block_compact_size l >= size /\
    (s |b= (var_e hmStart) == (nat_e adr)) /\
    (s |b= var_e result == null) /\
    (exists bloc_adr, 
      (s |b= (var_e entry) == (nat_e bloc_adr)) /\
      (
        (bloc_adr = 0 /\ (s |b= (var_e fnd) == (nat_e 0))) \/
        (bloc_adr = get_endl (l1 ++ Free_block_list l ++ l2) adr  /\
          (s |b= (var_e fnd) == nat_e 0) /\
          bloc_adr > 0) \/
        (exists bloc_size, exists bloc_status,
          bloc_adr > 0 /\
          In_hl (l1 ++ Free_block_list l ++ l2) (bloc_adr, bloc_size, bloc_status) adr /\ 
          (s |b= (var_e fnd) == nat_e 0)
        ) \/
        (exists bloc_size, bloc_size >= size /\
          In_hl (l1 ++ Free_block_list l ++ l2) (bloc_adr, bloc_size, free) adr /\ 
          (s |b= (var_e fnd) == nat_e 1) /\
          bloc_adr >0)))      
  ).

  (* while ((var_e entry =/= null) &&& (var_e fnd =/= int_e 1%Z)) precond-str *)

  red; intros.
  Decompose_hyp.

  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists adr.
  Resolve_topsy.
  right; right; left.

  destruct x.
  assert (Free_block_compact_size x1 > 0).
  omega.
  generalize (Free_block_list_nempty x1 H2); intros.
  destruct x1; try tauto.
  simpl in H1.
  exists n; exists true.
  split; auto.
  split.
  simpl.
  repeat rewrite <- beq_nat_refl.
  rewrite bool_eq_refl.
  simpl; trivial.
  Omega_exprb.
  destruct p.
  exists n; exists b.
  split; auto.
  split.
  simpl.
  repeat rewrite <- beq_nat_refl.
  rewrite bool_eq_refl.
  simpl; trivial.
  Omega_exprb.

  (* stts <-* entry -.> status; *)

  Step (fun s h => exists l1, exists l2, exists l,
    Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
    Free_block_compact_size l >= size /\
    (s |b= (var_e hmStart) == (nat_e adr)) /\
    (s |b= var_e result == null) /\
    (s |b= (var_e entry =/= null) &&& (var_e fnd =/= int_e 1%Z)) /\
    (exists bloc_adr, 
      (s |b= (var_e entry) == (nat_e bloc_adr)) /\
      (
        (bloc_adr = get_endl (l1 ++ Free_block_list l ++ l2) adr  /\
          (s |b= (var_e fnd) == nat_e 0) /\
          (s |b= (var_e stts) == Allocated) /\
          bloc_adr > 0) \/
        (exists bloc_size, exists bloc_status,
          bloc_adr > 0 /\
          In_hl (l1 ++ Free_block_list l ++ l2) (bloc_adr, bloc_size, bloc_status) adr /\ 
          (s |b= (var_e fnd) == nat_e 0) /\
          (s |b= (var_e stts) == hlstat_bool2expr bloc_status)
        )
      )
    )
  ).

  Decompose_hyp.
  inversion_clear H8.
  Decompose_hyp.
  assert (s |b= (var_e entry == null)).
  Omega_exprb.
  Omega_exprb.
  inversion_clear H1.
  Decompose_hyp.
  exists Allocated.
  apply cell_read.
  split.
  unfold status.
  generalize (hl_getstat' _ _ _ _ H2); intros.
  Decompose_sepcon H8 h1 h2.
  Compose_sepcon h1 h2; [Mapsto | red; auto].
  red.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists x2.
  Resolve_topsy.
  left.
  Resolve_topsy.
  inversion_clear H8.
  Decompose_hyp.
  generalize (In_hl_destruct _ _ _ _ _ H10); intro.
  Decompose_hyp.
  exists (hlstat_bool2expr x4).
  apply cell_read.
  split.
  unfold status.
  rewrite H9 in H2.
  generalize (hl_getstatus _ _ _ _ _ _ _ H2); intros.
  Decompose_sepcon H1 h1 h2.
  Compose_sepcon h1 h2; [Mapsto | red; auto].
  red.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists x2.
  Resolve_topsy.
  right.
  exists x3; exists x4.
  Resolve_topsy.
  destruct x4; rewrite <- expr_b_store_update_rewrite; auto.
  Decompose_hyp.
  Omega_exprb.

  (* ENTRYSIZE entry sz *)

  Step (fun s h => exists l1, exists l2, exists l,
    Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
    Free_block_compact_size l >= size /\
    (s |b= (var_e hmStart) == (nat_e adr)) /\
    (s |b= var_e result == null) /\
    (s |b= (var_e entry =/= null) &&& (var_e fnd =/= int_e 1%Z)) /\
    (exists bloc_adr, 
      (s |b= (var_e entry) == (nat_e bloc_adr)) /\
      (
        (bloc_adr = get_endl (l1 ++ Free_block_list l ++ l2) adr  /\
          (s |b= (var_e fnd) == nat_e 0) /\
          (s |b= (var_e stts) == Allocated) /\
          (s |b= (var_e sz) == nat_e 0) /\
          bloc_adr > 0) \/
        (exists bloc_size, exists bloc_status,
          bloc_adr > 0 /\
          In_hl (l1 ++ Free_block_list l ++ l2) (bloc_adr, bloc_size, bloc_status) adr /\ 
          (s |b= (var_e fnd) == nat_e 0) /\
          (s |b= (var_e stts) == hlstat_bool2expr bloc_status) /\
          (s |b= (var_e sz) == nat_e bloc_size)
        )
      )
    )
  ).
  unfold ENTRYSIZE.


  Step (fun s h => exists l1, exists l2, exists l,
    Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
    Free_block_compact_size l >= size /\
    (s |b= (var_e hmStart) == (nat_e adr)) /\
    (s |b= var_e result == null) /\
    (s |b= (var_e entry =/= null) &&& (var_e fnd =/= int_e 1%Z)) /\
    (exists bloc_adr, 
      (s |b= (var_e entry) == (nat_e bloc_adr)) /\
      (
        (bloc_adr = get_endl (l1 ++ Free_block_list l ++ l2) adr  /\
          (s |b= (var_e fnd) == nat_e 0) /\
          (s |b= (var_e stts) == Allocated) /\
          (s |b= (var_e sz) == nat_e 0) /\
          bloc_adr > 0) \/
        (exists bloc_size, exists bloc_status,
          bloc_adr > 0 /\
          In_hl (l1 ++ Free_block_list l ++ l2) (bloc_adr, bloc_size, bloc_status) adr /\ 
          (s |b= (var_e fnd) == nat_e 0) /\
          (s |b= (var_e stts) == hlstat_bool2expr bloc_status) /\
          (s |b= (var_e sz) == nat_e (bloc_size + 2 + bloc_adr))
        )
      )
    )
  ).

  Decompose_hyp.
  inversion_clear H8.
  Decompose_hyp.
  exists Allocated.
  apply cell_read.
  split.
  unfold next.
  generalize (hl_getnext' _ _ _ _ H1); intros.
  Decompose_sepcon H2 h1 h2.
  Compose_sepcon h1 h2; [Mapsto | red; auto].
  red.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists x2.
  Resolve_topsy.
  left.
  Resolve_topsy.
  Decompose_hyp.
  exists (nat_e (x2 + 2 + x3)).
  apply cell_read.
  generalize (In_hl_destruct _ _ _ _ _ H10); intro.
  Decompose_hyp.
  split.
  unfold next  .
  rewrite H11 in H1.
  generalize (hl_getnext _ _ _ _ _ _ _ H1); intros.
  Decompose_sepcon H2 h1 h2.
  Compose_sepcon h1 h2; [Mapsto | red; auto].
  red.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists x2.
  Resolve_topsy.
  right.
  exists x3; exists x4.
  Resolve_topsy.
  destruct x4; rewrite <- expr_b_store_update_rewrite; auto.

  Step (fun s h => exists l1, exists l2, exists l,
    Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
    Free_block_compact_size l >= size /\
    (s |b= (var_e hmStart) == (nat_e adr)) /\
    (s |b= var_e result == null) /\
    (s |b= (var_e entry =/= null) &&& (var_e fnd =/= int_e 1%Z)) /\
    (exists bloc_adr, 
      (s |b= (var_e entry) == (nat_e bloc_adr)) /\
      (
        (bloc_adr = get_endl (l1 ++ Free_block_list l ++ l2) adr  /\
          (s |b= (var_e fnd) == nat_e 0) /\
          (s |b= (var_e stts) == Allocated) /\
          (s |b= (nat_e 0) >>= (var_e sz)) /\
          bloc_adr > 0) \/
        (exists bloc_size, exists bloc_status,
          bloc_adr > 0 /\
          In_hl (l1 ++ Free_block_list l ++ l2) (bloc_adr, bloc_size, bloc_status) adr /\ 
          (s |b= (var_e fnd) == nat_e 0) /\
          (s |b= (var_e stts) == hlstat_bool2expr bloc_status) /\
          (s |b= (var_e sz) == nat_e bloc_size)
        )
      )
    )
  ).
  Decompose_hyp.
  inversion_clear H8.
  Decompose_hyp.
  red.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists x2.
  Resolve_topsy.
  left.
  Resolve_topsy.
  Decompose_hyp.
  red.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists x2.
  Resolve_topsy.
  right.
  exists x3; exists x4.
  Resolve_topsy.
  destruct x4; Resolve_topsy.
  rewrite <- expr_b_store_update_rewrite.
  Eval_b_hyp_clean.
  Eval_b_goal.
  rewrite H2.
  OmegaZ.

  Step TT.

  Step TT.
  intros.
  Decompose_hyp.
  inversion_clear H9.
  red.
  Decompose_hyp.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists x2.
  Resolve_topsy.
  left.
  Resolve_topsy.
  Decompose_hyp.
  red.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists x2.
  Resolve_topsy.
  right.
  exists x3; exists x4.
  Resolve_topsy.

  Step TT.

  red; intros.
  Decompose_hyp.
  inversion_clear H9.
  Decompose_hyp.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists x2.
  Resolve_topsy.
  left.
  Resolve_topsy.
  Decompose_hyp.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists x2.
  Resolve_topsy.
  right.
  exists x3; exists x4.
  Resolve_topsy.

  Step TT.

  Step TT.
  intros.
  Decompose_hyp.
  red.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists x2.
  Resolve_topsy.
  inversion_clear H9.
  Decompose_hyp.
  right; left.
  Resolve_topsy.
  Decompose_hyp.
  right; right; right.
  exists x3.
  split.
  Omega_exprb.
  Resolve_topsy.
  destruct x4.
  simpl hlstat_bool2expr in H12.
  auto.
  assert (s |b/= (var_e stts == Free) &&& (var_e sz >>= nat_e size)).
  Omega_exprb.
  Omega_exprb.

  Step TT.
  red; intros.
  Decompose_hyp.
  inversion_clear H9.
  Decompose_hyp.
  exists (nat_e 0).
  apply cell_read.
  split.
  unfold next.
  generalize (hl_getnext' _ _ _ _ H2); intros.
  Decompose_sepcon H1 h1 h2.
  Compose_sepcon h1 h2; [Mapsto | red; auto].
  red.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  exists 0.
  Resolve_topsy.
  left.
  Resolve_topsy.
  Decompose_hyp.
  exists (nat_e (x2 + 2 + x3)).
  apply cell_read.
  generalize (In_hl_destruct _ _ _ _ _ H11); intro.
  Decompose_hyp.
  rewrite H13 in H2.
  split.
  unfold next.
  generalize (hl_getnext _ _ _ _ _ _ _ H2); intros.
  Decompose_sepcon H1 h1 h2.
  Compose_sepcon h1 h2; [Mapsto | red; auto].
  red.
  exists x; exists x0; exists x1.
  rewrite H13.
  Resolve_topsy.
  exists (x2 + 2 + x3).
  Resolve_topsy.
  destruct x6.
  right; left.
  Resolve_topsy.
  rewrite get_endl_app.
  simpl; omega.
  omega.
  destruct p.
  right; right; left.
  exists n; exists b.
  split.
  omega.
  split.
  apply In_hl_or_app.
  right.
  simpl.
  assert (x2 <> x2 + 2 + x3).
  omega.
  rewrite H15.
  rewrite (beq_dif_false _ _ H1); simpl.
  repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
  Resolve_topsy.

  (* while ((var_e entry =/= null) &&& (var_e fnd =/= int_e 1%Z)) precond-weak *)

  red; intros.
  Decompose_hyp.
  inversion_clear H8.
  Decompose_hyp.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  Omega_exprb.
  Omega_exprb.
  right.
  Omega_exprb.
  inversion_clear H1.
  Decompose_hyp.
  Omega_exprb_contradiction.
  inversion_clear H8.
  Decompose_hyp.
  Omega_exprb_contradiction.
  Decompose_hyp.
  exists x; exists x0; exists x1.
  Resolve_topsy.
  Omega_exprb.
  Omega_exprb.
  left.
  exists x2; exists x3.
  Resolve_topsy.
  Omega_exprb.
Qed.



  (* we perform a compaction => we now for sure that a big enough free block for the allocation exists *)

Definition compact_specif2:= forall adr size,
  size > 0 ->
  adr > 0 ->

  {{fun s => fun h => exists l1, exists l2, exists l,  
    (Heap_List (l1 ++ (Free_block_list l) ++ l2) adr) s h /\
    (Free_block_compact_size l) >= size /\
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\
    eval (var_e cptr) s = eval (nat_e adr) s
  }}
  
  compact cptr nptr stts
  
  {{fun s => fun h => exists l,  
    (Heap_List l adr) s h /\
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\
    (exists free_adr, exists free_size, free_size >= size /\
      In_hl l (free_adr, free_size, free) adr
    )
  }}.



Lemma compact_verif2: compact_specif2.
  unfold compact_specif2.
  intros.
  unfold compact.

  (* First loop invariant *)

  Step (

    fun (s : store.s) (h : heap.h) =>
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e result) s = eval null s /\
      exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
        (
          (exists l1,
            exists l,
              exists l2,
                exists free_size,
                  Heap_List (l1 ++ (free_size,free)::(Free_block_list l) ++ l2) adr s h /\
                  Free_block_compact_size (free_size::l) >= size /\
                (
                  (cur_adr > 0 /\
                    exists cur_size,
                      exists cur_status, 
                        In_hl l1 (cur_adr, cur_size, cur_status) adr) \/
                  (cur_adr > 0 /\ cur_adr = get_endl l1 adr) \/
                  (cur_adr > 0 /\ l = nil /\ 
                    exists cur_size, 
                      exists cur_status, 
                        In_hl l2 (cur_adr, cur_size, cur_status) (get_endl (l1++(free_size,free)::nil) adr)) \/
                  (cur_adr > 0 /\ l = nil /\ 
                    cur_adr = (get_endl (l1++(free_size,free)::l2) adr)) \/
                  (l = nil /\ 
                    cur_adr = 0)
                )
          )
        )
  ).

  (* First loop invariant PS *)

  red; intros.
  Decompose_hyp.
  Resolve_topsy.
  exists adr.
  Resolve_topsy.
  lapply (Free_block_list_nempty x1); [intros | omega].
  destruct x1; try tauto.
  exists x; exists x1; exists x0; exists n.
  Resolve_topsy.
  destruct x.
  right; left; auto.
  destruct p.
  left.
  Resolve_topsy.
  exists n0; exists b.
  simpl.
  repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.

  (* stts <-* cptr -.> status;  *)
  
  Step (

    fun (s : store.s) (h : heap.h) =>
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e result) s = eval null s /\
      exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
        (
          (exists l1,
            exists l,
              exists l2,
                exists free_size,
                  Heap_List (l1 ++ (free_size,free)::(Free_block_list l) ++ l2) adr s h /\
                  Free_block_compact_size (free_size::l) >= size /\
                (
                  (cur_adr > 0 /\
                    exists cur_size,
                      exists cur_status, 
                        In_hl l1 (cur_adr, cur_size, cur_status) adr /\
                        (s |b= var_e stts == (hlstat_bool2expr cur_status))
                  ) \/
                  (cur_adr > 0 /\ cur_adr = get_endl l1 adr /\
                    (s |b= var_e stts == (hlstat_bool2expr free))
                  ) \/
                  (cur_adr > 0 /\ l = nil /\ 
                    exists cur_size, 
                      exists cur_status, 
                        In_hl l2 (cur_adr, cur_size, cur_status) (get_endl (l1++(free_size,free)::nil) adr) /\
                        (s |b= var_e stts == (hlstat_bool2expr cur_status))
                  ) \/
                  (cur_adr > 0 /\ l = nil /\ 
                    cur_adr = (get_endl (l1++(free_size,free)::l2) adr) /\
                    (s |b= var_e stts == (hlstat_bool2expr alloc))
                  )
                )
          )
        )
  ).

  Decompose_hyp.
  inversion_clear H9; Decompose_hyp.

  exists (hlstat_bool2expr x5).
  unfold status.
  apply cell_read.
  split.
  In_hl_destruct_hyp H9.
  Hl_getstatus H1 x4.
  Mapsto.
  red.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
  exists x.
  Resolve_topsy.
  exists x0; exists x1; exists x2; exists x3.
  Resolve_topsy.
  left.
  Resolve_topsy.
  exists x4; exists x5.
  Resolve_topsy.
  destruct x5; rewrite <- expr_b_store_update_rewrite; auto.
  
  inversion_clear H6; Decompose_hyp.

  exists (hlstat_bool2expr free).
  unfold status.
  apply cell_read.
  split.
  Hl_getstatus H1 x3.
  Mapsto.
  red.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
  exists x.
  Resolve_topsy.
  exists x0; exists x1; exists x2; exists x3.
  Resolve_topsy.
  right; left.
  Resolve_topsy.

  inversion_clear H7; Decompose_hyp.

  exists (hlstat_bool2expr x5).
  unfold status.
  apply cell_read.
  split.
  In_hl_destruct_hyp H9.
  Hl_getstatus H1 x4.
  subst x1.
  simpl Free_block_list in H14.
  repeat rewrite get_endl_app in H12; simpl in H12.
  repeat rewrite get_endl_app in H14; simpl in H14.
  Mapsto.
  red.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
  exists x.
  Resolve_topsy.
  exists x0; exists x1; exists x2; exists x3.
  Resolve_topsy.
  right; right; left.
  Resolve_topsy.
  exists x4; exists x5.
  Resolve_topsy.
  destruct x5; rewrite <- expr_b_store_update_rewrite; auto.
  
  inversion_clear H6; Decompose_hyp.
  
  subst x1; simpl Free_block_list in H1.
  exists (hlstat_bool2expr alloc).
  unfold status.
  apply cell_read.
  split.
  Hl_getstat' H1.
  Mapsto.
  red.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
  exists x.
  Resolve_topsy.
  exists x0; exists (@nil nat); exists x2; exists x3.
  Resolve_topsy.
  right; right; right.
  Resolve_topsy.

  Omega_exprb_contradiction.
  
  (* (ifte var_e stts == Free) Post condition  *)

  Step (

    fun (s : store.s) (h : heap.h) =>
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e result) s = eval null s /\
      exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
        (
          (exists l1,
            exists l,
              exists l2,
                exists free_size,
                  Heap_List (l1 ++ (free_size,free)::(Free_block_list l) ++ l2) adr s h /\
                  Free_block_compact_size (free_size::l) >= size /\
                (
                  (cur_adr > 0 /\
                    exists cur_size,
                      exists cur_status, 
                      In_hl l1 (cur_adr, cur_size, cur_status) adr
                  ) \/
                  (cur_adr > 0 /\ cur_adr = get_endl l1 adr /\ l = nil
                  ) \/
                  (cur_adr > 0 /\ l = nil /\ 
                    exists cur_size, 
                      exists cur_status, 
                        In_hl l2 (cur_adr, cur_size, cur_status) (get_endl (l1++(free_size,free)::nil) adr)
                  ) \/
                  (cur_adr > 0 /\ l = nil /\ 
                    cur_adr = (get_endl (l1++(free_size,free)::l2) adr)
                  )
                )
          )
        )
  ).

  (* nptr <-* cptr -.> next; *)


  Step (

    fun (s : store.s) (h : heap.h) =>
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e result) s = eval null s /\
      exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
        (
          (exists l1,
            exists l,
              exists l2,
                exists free_size,
                  Heap_List (l1 ++ (free_size,free)::(Free_block_list l) ++ l2) adr s h /\
                  Free_block_compact_size (free_size::l) >= size /\
                (
                  (cur_adr > 0 /\ 
                    exists cur_size,
                      In_hl l1 (cur_adr, cur_size, free) adr /\
                      (s |b= var_e nptr == nat_e (cur_adr + 2 + cur_size))
                  ) \/
                  (cur_adr > 0 /\ cur_adr = get_endl l1 adr /\
                    (s |b= var_e nptr == nat_e (cur_adr + 2 + free_size))
                  ) \/
                  (l = nil /\ cur_adr > 0 /\
                    exists cur_size, 
                      In_hl l2 (cur_adr, cur_size, free) (get_endl (l1++(free_size,free)::nil) adr) /\
                      (s |b= var_e nptr == nat_e (cur_adr + 2 + cur_size))
                  )
                )
          )
        )
  ).

  Decompose_hyp.
  inversion_clear H9; Decompose_hyp.

  unfold next.
  exists (nat_e (x + 2 + x4)).
  apply cell_read.
  split.
  In_hl_destruct_hyp H6.
  Hl_getnext H1 x4.
  Mapsto.
  red.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
  exists x.
  Resolve_topsy.
  exists x0; exists x1; exists x2; exists x3.
  Resolve_topsy.
  left.
  Resolve_topsy.  
  exists x4.
  Resolve_topsy.  
  destruct x5; [auto | Omega_exprb_contradiction].

  inversion_clear H6; Decompose_hyp.
  
  unfold next.
  exists (nat_e (x + 2 + x3)).
  apply cell_read.
  split.
  Hl_getnext H1 x3.
  Mapsto.
  red.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
  exists x.
  Resolve_topsy.
  exists x0; exists x1; exists x2; exists x3.
  Resolve_topsy.
  right; left.
  Resolve_topsy.  

  inversion_clear H7; Decompose_hyp.
  unfold next.
  exists (nat_e (x + 2 + x4)).
  apply cell_read.
  split.
  subst x1; simpl Free_block_list in H1.
  In_hl_destruct_hyp H6.
  Hl_getnext H1 x4.
  repeat rewrite get_endl_app in H12; simpl in H12.
  repeat rewrite get_endl_app in H14; simpl in H14.
  Mapsto.
  red.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
  exists x.
  Resolve_topsy.
  exists x0; exists x1; exists x2; exists x3.
  Resolve_topsy.
  right; right.
  Resolve_topsy.
  exists x4.
  Resolve_topsy.
  destruct x5; [auto | Omega_exprb_contradiction].

  Omega_exprb_contradiction.

  (* stts <-* nptr -.> status; *)

  Step (

    fun (s : store.s) (h : heap.h) =>
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e result) s = eval null s /\
      exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
        (
          (exists l1,
            exists l,
              exists l2,
                exists free_size,
                  Heap_List (l1 ++ (free_size,free)::(Free_block_list l) ++ l2) adr s h /\
                  Free_block_compact_size (free_size::l) >= size /\
                (
                  (cur_adr > 0 /\ exists cur_size,
                    In_hl l1 (cur_adr, cur_size, free) adr /\
                    (s |b= var_e nptr == nat_e (cur_adr + 2 + cur_size)) /\
                    (
                      (exists next_status, 
                        exists next_size, 
                          In_hl l1 (cur_adr + 2 + cur_size, next_size, next_status) adr /\
                          (s |b= var_e stts == (hlstat_bool2expr next_status))
                      ) \/
                      (cur_adr + 2 + cur_size = get_endl l1 adr /\
                        (s |b= var_e stts == (hlstat_bool2expr free))                        
                      )
                    )
                  ) \/
                  (cur_adr = get_endl l1 adr /\ cur_adr > 0 /\
                    (s |b= var_e nptr == nat_e (cur_adr + 2 + free_size)) /\
                    (
                      (l = nil /\ 
                        exists next_status, 
                          exists next_size, 
                            In_hl l2 (cur_adr + 2 + free_size, next_size, next_status) (get_endl (l1++(free_size,free)::nil) adr) /\
                            (s |b= var_e stts == (hlstat_bool2expr next_status))
                      ) \/
                      (l <> nil /\
                        exists hd, 
                          exists tl, 
                            l = hd::tl /\
                            (s |b= var_e stts == (hlstat_bool2expr free))
                      ) \/ 
                      (l = nil /\ 
                        cur_adr + 2 + free_size = get_endl (l1 ++ (free_size,free)::nil) adr /\
                        (s |b= var_e stts == (hlstat_bool2expr alloc))
                      )
                    )
                  ) \/
                  (l = nil /\ cur_adr > 0 /\
                    exists cur_size, 
                      In_hl l2 (cur_adr, cur_size, free) (get_endl (l1++(free_size,free)::nil) adr) /\
                      (s |b= var_e nptr == nat_e (cur_adr + 2 + cur_size)) /\
                      (
                        (
                          exists next_status, 
                          exists next_size, 
                            In_hl l2 (cur_adr + 2 + cur_size, next_size, next_status) (get_endl (l1++(free_size,free)::nil) adr) /\
                            (s |b= var_e stts == (hlstat_bool2expr next_status))
                        ) \/
                        (cur_adr + 2 + cur_size = get_endl (l1 ++ (free_size,free)::l2) adr /\
                          (s |b= var_e stts == (hlstat_bool2expr alloc))
                        )
                        
                      )                      
                  )
                )
          )
        )
  ).

(* L *)

Decompose_hyp.
unfold status.
inversion_clear H8; Decompose_hyp.

In_hl_destruct_hyp H8.
destruct x6.
exists (hlstat_bool2expr free).
apply cell_read.
split.
Hl_getstatus H1 x3.
clear H16.
rewrite get_endl_app in H13; simpl in H13.
rewrite <- H11 in H9.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists x5; exists (x3::x1); exists x2.
exists x4.
simpl Free_block_list.
Cutrewrite_hyp H1 ((x5 ++ (x4, free) :: nil) ++ (x3, free) :: Free_block_list x1 ++ x2 = x5 ++ (x4, free) :: ((x3, true) :: Free_block_list x1) ++ x2).
List_eq.
Resolve_topsy.
unfold Free_block_compact_size in H7; unfold Free_block_compact_size; simpl; simpl in H7.
omega.
right; left.
Resolve_topsy.
right; left.
Resolve_topsy.
red; intros; discriminate.
exists x3; exists x1.
Resolve_topsy.
destruct p.
exists (hlstat_bool2expr b).
apply cell_read.
split.
Hl_getstatus H1 n.
clear H16.
rewrite get_endl_app in H13; simpl in H13.
rewrite <- H11 in H9.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists (x5 ++ (x4, free) :: (n, b) :: x6); exists x1; exists x2; exists x3.
Resolve_topsy.
left.
Resolve_topsy.
exists x4.
Resolve_topsy.
left.
exists b; exists n.
Resolve_topsy.
apply In_hl_or_app.
right.
simpl.
destruct (beq_nat (get_endl x5 adr) (x + 2 + x4) && bool_eq b free && beq_nat x4 n); simpl; auto.
rewrite H11; repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
destruct b; rewrite <- expr_b_store_update_rewrite; auto.

inversion_clear H5; Decompose_hyp.
destruct x1.
simpl in H1.
destruct x2.
exists (hlstat_bool2expr alloc).
apply cell_read.
split.
Hl_getstat' H1.
rewrite get_endl_app in H12; clear H15; simpl in H12.
rewrite H9 in H10.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists x0; exists (@nil nat); exists (@nil (nat * bool)); exists x3.
Resolve_topsy.
right; left.
Resolve_topsy.
right; right.
Resolve_topsy.
rewrite get_endl_app; simpl; omega.

destruct p.
exists (hlstat_bool2expr b).
apply cell_read.
split.
Hl_getstatus H1 n.
clear H15.
rewrite get_endl_app in H12; simpl in H12.
rewrite H9 in H10.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists x0; exists (@nil nat); exists ((n,b)::x2); exists x3.
Resolve_topsy.
right; left.
Resolve_topsy.
left.
Resolve_topsy.
exists b; exists n.
Resolve_topsy.
simpl.
rewrite get_endl_app; simpl.
rewrite H9; repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
destruct b; rewrite <- expr_b_store_update_rewrite; auto.

simpl in H1.
exists (hlstat_bool2expr free).
apply cell_read.
split.
Hl_getstatus H1 n.
clear H15.
rewrite get_endl_app in H12; simpl in H12.
rewrite H9 in H10; Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists x0; exists (n::x1); exists x2; exists x3.
Resolve_topsy.
right; left.
Resolve_topsy.
right; left.
Resolve_topsy.
red; intros; discriminate.
exists n; exists x1.
Resolve_topsy.

subst x1; simpl in H1.
In_hl_destruct_hyp H8.
destruct x5.
exists (hlstat_bool2expr alloc).
apply cell_read.
split.
Hl_getstat' H1.
clear H16.
repeat rewrite get_endl_app in H13; simpl in H13.
repeat rewrite get_endl_app in H13; simpl in H13.
repeat rewrite get_endl_app in H11; simpl in H11.
rewrite <- H11 in H10; Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists x0; exists (@nil nat); exists (x1 ++ (x4,free)::nil); exists x3.
Resolve_topsy.
right; right.
Resolve_topsy.
exists x4.
Resolve_topsy.
right.
split.
rewrite <- H11.
repeat rewrite get_endl_app; simpl; repeat rewrite get_endl_app; auto.
rewrite <- expr_b_store_update_rewrite; auto.

destruct p.
exists (hlstat_bool2expr b).
apply cell_read.
split.
Hl_getstatus H1 n.
clear H16.
do 2 (rewrite get_endl_app in H13; simpl in H13).
(rewrite get_endl_app in H11; simpl in H11).
rewrite H11 in H13.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists x0; exists (@nil nat); exists (x1 ++ (x4,free)::(n,b)::x5); exists x3.
Resolve_topsy.
right; right.
Resolve_topsy.
exists x4.
Resolve_topsy.
left.
exists b; exists n.
split.
eapply In_hl_or_app; right; simpl.
destruct (beq_nat (get_endl x1 (get_endl (x0 ++ (x3, free) :: nil) adr)) (x + 2 + x4) && bool_eq b free && beq_nat x4 n); simpl; auto.
rewrite H11; repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
destruct b; rewrite <- expr_b_store_update_rewrite; auto.

(* Second loop invariant *)


  Step (

    fun (s : store.s) (h : heap.h) =>
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e result) s = eval null s /\
      exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
        (
          (exists l1,
            exists l,
              exists l2,
                exists free_size,
                  Heap_List (l1 ++ (free_size,free)::(Free_block_list l) ++ l2) adr s h /\
                  Free_block_compact_size (free_size::l) >= size /\
                (
                  (cur_adr > 0 /\ 
                    exists cur_size,
                      In_hl l1 (cur_adr, cur_size, free) adr /\
                      (s |b= var_e nptr == nat_e (cur_adr + 2 + cur_size)) /\
                      (
                        (exists next_status, 
                          exists next_size, 
                            In_hl l1 (cur_adr + 2 + cur_size, next_size, next_status) adr /\
                            (s |b= var_e stts == (hlstat_bool2expr next_status))
                        ) \/
                        (cur_adr + 2 + cur_size = get_endl l1 adr /\
                          (s |b= var_e stts == (hlstat_bool2expr free))                        
                        )
                      )
                  ) \/
                  (cur_adr = get_endl l1 adr /\ cur_adr > 0 /\
                    (s |b= var_e nptr == nat_e (cur_adr + 2 + free_size)) /\
                    (
                      (l = nil /\ 
                        exists next_status, 
                          exists next_size, 
                            In_hl l2 (cur_adr + 2 + free_size, next_size, next_status) (get_endl (l1++(free_size,free)::nil) adr) /\
                            (s |b= var_e stts == (hlstat_bool2expr next_status))
                      ) \/
                      (l <> nil /\
                        exists hd, 
                          exists tl, 
                            l = hd::tl /\
                            (s |b= var_e stts == (hlstat_bool2expr free))
                      )  \/ 
                      (l = nil /\ 
                        cur_adr + 2 + free_size = get_endl (l1 ++ (free_size,free)::nil) adr /\
                        (s |b= var_e stts == (hlstat_bool2expr alloc))
                      )
                    )
                  ) \/
                  (l = nil /\ cur_adr > 0 /\
                    exists cur_size, 
                      In_hl l2 (cur_adr, cur_size, free) (get_endl (l1++(free_size,free)::nil) adr) /\
                      (s |b= var_e nptr == nat_e (cur_adr + 2 + cur_size)) /\
                      (
                        (
                          exists next_status, 
                          exists next_size, 
                            In_hl l2 (cur_adr + 2 + cur_size, next_size, next_status) (get_endl (l1++(free_size,free)::nil) adr) /\
                            (s |b= var_e stts == (hlstat_bool2expr next_status))
                        ) \/
                        (cur_adr + 2 + cur_size = get_endl (l1 ++ (free_size,free)::l2) adr /\
                          (s |b= var_e stts == (hlstat_bool2expr alloc))
                        )
                        
                      )                      
                  )
                )
          )
        )
  ).

(* Second loop PS *)

red; intros.
Decompose_hyp.
Resolve_topsy.
exists x.
Resolve_topsy.
exists x0; exists x1; exists x2; exists x3.
Resolve_topsy.

(* stts <-* nptr -.> next; *)


  Step (

    fun (s : store.s) (h : heap.h) =>
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e result) s = eval null s /\
      exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
        (
          (exists l1,
            exists l,
              exists l2,
                exists free_size,
                  Heap_List (l1 ++ (free_size,free)::(Free_block_list l) ++ l2) adr s h /\
                  Free_block_compact_size (free_size::l) >= size /\
                (
                  (cur_adr > 0 /\ 
                    exists cur_size,
                      In_hl l1 (cur_adr, cur_size, free) adr /\
                      (s |b= var_e nptr == nat_e (cur_adr + 2 + cur_size)) /\
                      (
                        (exists next_size, 
                          In_hl l1 (cur_adr + 2 + cur_size, next_size, free) adr /\
                          (s |b= var_e stts == nat_e (cur_adr + 2 + cur_size + 2 + next_size))
                        ) \/
                        (cur_adr + 2 + cur_size = get_endl l1 adr /\
                          (s |b= var_e stts == nat_e (cur_adr + 2 + cur_size + 2 + free_size))
                        )
                      )
                  ) \/
                  (cur_adr = get_endl l1 adr /\ cur_adr > 0 /\ 
                    (s |b= var_e nptr == nat_e (cur_adr + 2 + free_size)) /\
                    (
                      (l = nil /\ 
                        exists next_size, 
                          In_hl l2 (cur_adr + 2 + free_size, next_size, free) (get_endl (l1++(free_size,free)::nil) adr) /\
                          (s |b= var_e stts == nat_e (cur_adr + 2 + free_size + 2 + next_size))
                      ) \/
                      (l <> nil  /\
                        exists hd, 
                          exists tl, 
                            l = hd::tl /\
                            (s |b= var_e stts == nat_e (cur_adr + 2 + free_size + 2 + hd))
                      )
                    )
                  ) \/
                  (l = nil /\ cur_adr > 0 /\ 
                    exists cur_size, 
                      In_hl l2 (cur_adr, cur_size, free) (get_endl (l1++(free_size,free)::nil) adr) /\
                      (s |b= var_e nptr == nat_e (cur_adr + 2 + cur_size)) /\
                      (
                        (
                          exists next_size, 
                            In_hl l2 (cur_adr + 2 + cur_size, next_size, free) (get_endl (l1++(free_size,free)::nil) adr) /\
                            (s |b= var_e stts == nat_e (cur_adr + 2 + cur_size + 2 + next_size))
                        )                         
                      )                      
                  )
                )
          )
        )
  ).

  Decompose_hyp.
  unfold next.
  inversion_clear H9; Decompose_hyp.
  inversion_clear H12; Decompose_hyp.

  exists (nat_e (x + 2 + x4 + 2 + x6)).
  apply cell_read.
  split.
  In_hl_destruct_hyp H10.
  Hl_getnext H1 x6.
  rewrite <- H14 in H11.
  Mapsto.
  red.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
  exists x.
  Resolve_topsy.
  exists x0; exists x1; exists x2; exists x3.
  Resolve_topsy.
  left.
  Resolve_topsy.
  exists x4.
  Resolve_topsy.
  left.
  exists x6.
  Resolve_topsy.
  destruct x5; [auto | Omega_exprb_contradiction].

  exists (nat_e (x + 2 + x4 + 2 + x3)).
  apply cell_read.
  split.
  Hl_getnext H1 x3.
  rewrite H10 in H11.
  Mapsto.
  red.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
  exists x.
  Resolve_topsy.
  exists x0; exists x1; exists x2; exists x3.
  Resolve_topsy.
  left.
  Resolve_topsy.
  exists x4.
  Resolve_topsy.
  right.
  Resolve_topsy.

  inversion_clear H6; Decompose_hyp.
  inversion_clear H12; Decompose_hyp.
  exists (nat_e (x + 2 + x3 + 2 + x5)).
  apply cell_read.
  split.
  In_hl_destruct_hyp H7.
  Hl_getnext H1 x5.
  subst x1; simpl Free_block_list in H17.
  repeat rewrite get_endl_app in H17; simpl in H17.
  repeat rewrite get_endl_app in H15; simpl in H15.
  rewrite <- H15 in H9.
  Mapsto.
  red.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
  exists x.
  Resolve_topsy.  
  exists x0; exists x1; exists x2; exists x3.
  Resolve_topsy.
  right; left.
  Resolve_topsy.
  left.
  Resolve_topsy.
  exists x5.
  Resolve_topsy.
  destruct x4; [auto | Omega_exprb_contradiction].

  inversion_clear H7; Decompose_hyp.
  
  exists (nat_e (x + 2 + x3 + 2 + x4)).
  apply cell_read.
  split.
  rewrite H11 in H1.
  simpl in H1.
  Hl_getnext H1 x4.
  clear H19.
  rewrite get_endl_app in H16; simpl in H16.
  rewrite <- H6 in H16.
  Mapsto.
  clear H13.
  Eval_b_hyp H9.
  rewrite H13; OmegaZ.
  red.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
  exists x.
  Resolve_topsy.  
  exists x0; exists x1; exists x2; exists x3.
  Resolve_topsy.
  right; left.
  Resolve_topsy.
  right.
  Resolve_topsy.
  exists x4; exists x5.
  Resolve_topsy.
  
  Omega_exprb_contradiction.

  inversion_clear H13; Decompose_hyp.
  exists (nat_e (x + 2 + x4 + 2 + x6)).
  apply cell_read.
  split.
  repeat rewrite get_endl_app in H11; simpl in H11.  
  subst x1; simpl in H1.
  In_hl_destruct_hyp H11.
  Hl_getnext H1 x6.
  repeat rewrite get_endl_app in H16; simpl in H16.  
  Mapsto.
  clear H13.
  Eval_b_hyp H12.
  rewrite H14.
  OmegaZ.
  red.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
  exists x.
  Resolve_topsy.  
  exists x0; exists x1; exists x2; exists x3.
  Resolve_topsy.
  right; right.
  Resolve_topsy.
  exists x4.  
  Resolve_topsy.
  exists x6.
  Resolve_topsy.
  destruct x5; [auto | Omega_exprb_contradiction].
  Omega_exprb_contradiction.

(* cptr -.> next *<- var_e stts;*)

  Step (

    fun (s : store.s) (h : heap.h) =>
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e result) s = eval null s /\
      exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
        (
          (exists l1,
            exists l,
              exists l2,
                exists free_size,
                  Heap_List (l1 ++ (free_size,free)::(Free_block_list l) ++ l2) adr s h /\
                  Free_block_compact_size (free_size::l) >= size /\
                (
                  (cur_adr > 0 /\ 
                    exists cur_size,
                      In_hl l1 (cur_adr, cur_size, free) adr /\
                      (s |b= var_e stts == nat_e (cur_adr + 2 + cur_size))
                  ) \/
                  (cur_adr > 0 /\ cur_adr = get_endl l1 adr /\
                    (s |b= var_e stts == nat_e (cur_adr + 2 + free_size))
                  ) \/
                  (l = nil /\ cur_adr > 0 /\
                    exists cur_size, 
                      In_hl l2 (cur_adr, cur_size, free) (get_endl (l1++(free_size,free)::nil) adr) /\
                      (s |b= var_e stts == nat_e (cur_adr + 2 + cur_size))
                  )
                )
          )
        )
  ).

unfold next.
Decompose_hyp.
inversion_clear H8; Decompose_hyp.
inversion_clear H11; Decompose_hyp.
generalize (In_hl_next x0 x x4 free x5 free adr H8 H5); intros.
Decompose_hyp.
rewrite H12 in H1.

Cutrewrite_hyp H1 (
(x6 ++ (x4, free) :: (x5, free) :: x7) ++ (x3, free) :: Free_block_list x1 ++ x2 =
x6 ++ (x4, free) :: (x5, free) ::nil ++ x7 ++ (x3, free) :: Free_block_list x1 ++ x2
).
List_eq.
generalize (hl_compaction x6 (x7 ++ (x3, free) :: Free_block_list x1 ++ x2) x4 x5 adr s h H1); intros.
inversion_clear H9.
Decompose_sepcon H14 h1 h2.
exists x8; Compose_sepcon h1 h2.
rewrite <- H13 in H14.
simpl in H3.
Mapsto.
red; intros.
rewrite <- H13 in H17.
clear H1.
assert (h2 # h' /\ (nat_e (x + 1) |-> nat_e (x + x4 + x5 + 4)) s h').
inversion_clear H16.
split; [auto | Mapsto].
Eval_b_hyp H11.
rewrite H16.
OmegaZ.
red in H17.
generalize (H17 h' H1 h'' H18); clear H17; intros.
simpl in H17.

Resolve_topsy.
exists x.
Resolve_topsy.
exists (x6 ++ (x4 + x5 + 2, free):: x7); exists x1; exists x2; exists x3.
Resolve_topsy.
List_eq.
left.
Resolve_topsy.
exists (x4 + x5 + 2).
Resolve_topsy.
apply In_hl_or_app; right.
simpl.
rewrite <- H13; repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
Eval_b_hyp H11.
Eval_b_goal.
rewrite H19.
OmegaZ.

generalize (In_hl_last _ _ _ _ _ H8 (sym_eq H9)); intros.
Decompose_hyp.
subst x0.
Cutrewrite_hyp H1 (
(x5 ++ (x4, free) :: nil) ++ (x3, free) :: Free_block_list x1 ++ x2 =
x5 ++ (x4, free)::(x3, free)::nil ++ Free_block_list x1 ++ x2).
List_eq.
generalize (hl_compaction x5 (Free_block_list x1 ++ x2) x4 x3 adr s h H1); intros.
inversion_clear H5.
clear H1.
Decompose_sepcon H12 h1 h2.
exists x0.
Compose_sepcon h1 h2.
rewrite get_endl_app in H9.
simpl in H9.
Mapsto.
red; intros.
assert (h2 # h' /\ (nat_e (x + 1) |-> nat_e (x + x4 + x3 + 4)) s h').
inversion_clear H13.
split; [auto | Mapsto].
Eval_b_hyp H11.
rewrite H13.
OmegaZ.
rewrite get_endl_app in H9.
simpl in H9.
Cutrewrite_hyp H14 (get_endl x5 adr = x).
omega.
generalize (H14 h' H16 h'' H15); clear H16 H14; intros.
Resolve_topsy.
exists x.
Resolve_topsy.
exists (x5); exists x1; exists x2; exists (x4 + x3 + 2).
Resolve_topsy.
unfold Free_block_compact_size in H7; simpl in H7.
unfold Free_block_compact_size; simpl.
omega.
right; left.
Resolve_topsy.
omega.
Eval_b_hyp H11.
Eval_b_goal.
rewrite H16.
OmegaZ.

inversion_clear H5; Decompose_hyp.
inversion_clear H11; Decompose_hyp.

rewrite get_endl_app in H11.
simpl in H11.
rewrite <- H5 in H11.

generalize (In_hl_first _ _ _ _ H11); intros; Decompose_hyp.
subst x2 x1.
simpl in H1.
Cutrewrite_hyp H1 (x0 ++ (x3, free) :: (x4, free) :: x5 = x0 ++ (x3, free) :: (x4, free) :: nil ++ x5).
List_eq.
generalize (hl_compaction _ _ _ _  adr s h H1); intros.
Decompose_hyp.
exists x1.
Compose_sepcon H6 H10.
Mapsto.
red; intros.
assert (H10 # h' /\ ((nat_e (get_endl x0 adr + 1) |-> nat_e (get_endl x0 adr + x3 + x4 + 4)) s h')).
subst x.
split; intuition.
Mapsto.
Eval_b_hyp H12.
OmegaZ.
generalize (H17 _ H19 _ H18); intros.
clear H14 H17 H16 H19.
Resolve_topsy.
exists x.
Resolve_topsy.
exists x0; exists (@nil nat); exists x5; exists (x3 + x4 + 2).
Resolve_topsy.
unfold Free_block_compact_size in H7; simpl in H7.
unfold Free_block_compact_size; simpl; omega.
right; left.
Resolve_topsy.
Eval_b_hyp H12.
Eval_b_goal.
OmegaZ.

subst x1.
clear H10.
simpl in H1.
Cutrewrite_hyp H1 (x0 ++ (x3, free) :: (x4, true) :: Free_block_list x5 ++ x2 = x0 ++ (x3, free) :: (x4, true) :: nil ++ Free_block_list x5 ++ x2).
List_eq.
generalize (hl_compaction _ _ _ _  adr s h H1); intros.
Decompose_hyp.
exists x1; Compose_sepcon H6 H10.
Mapsto.
red; intros.
assert (H10 # h' /\ (nat_e (get_endl x0 adr + 1) |-> nat_e (get_endl x0 adr + x3 + x4 + 4)) s h').
split; intuition.
Mapsto.
Eval_b_hyp H12; OmegaZ.
clear H13; clear H15.
generalize (H16 _ H18 _ H17); clear H16 H18; intros.
Resolve_topsy.
exists x.
Resolve_topsy.
exists x0; exists x5; exists x2; exists (x3 + x4 + 2); simpl in H13.
Resolve_topsy.
unfold Free_block_compact_size in H7; simpl in H7; unfold Free_block_compact_size; simpl; omega.
right; left.
Resolve_topsy.
Eval_b_hyp H12.
Eval_b_goal.
OmegaZ.

subst x1.
generalize (In_hl_next _ _ _ _ _ _ _ H8 H10); intros.
Decompose_hyp.
clear H8; clear H10.
subst x2.
simpl in H1.
Cutrewrite_hyp H1 (
x0 ++ (x3, free) :: x1 ++ (x4, free) :: (x5, free) :: x6 =
(x0 ++ (x3, free) :: x1) ++ (x4, free) :: (x5, free) :: nil ++ x6
).
repeat List_eq.
generalize (hl_compaction _ _ _ _  adr s h H1); intros.
Decompose_hyp.
exists x2.
Compose_sepcon H5 H6.
Mapsto.
simpl in H3.
rewrite H3.
repeat rewrite get_endl_app; simpl.
repeat rewrite get_endl_app in H13; simpl in H13.
OmegaZ.
red; intros.
Resolve_topsy.
exists x.
Resolve_topsy.
clear H10.
assert (H6 # h' /\ (nat_e (get_endl (x0 ++ (x3, free) :: x1) adr + 1)
         |-> nat_e (get_endl (x0 ++ (x3, free) :: x1) adr + x4 + x5 + 4)) s h').
intuition.
Mapsto.
simpl in H3; rewrite H3.
repeat rewrite get_endl_app; simpl.
repeat rewrite get_endl_app in H13; simpl in H13.
OmegaZ.
Eval_b_hyp H12.
repeat rewrite get_endl_app; simpl.
repeat rewrite get_endl_app in H13; simpl in H13.
OmegaZ.
generalize (H16 _ H10 _ H17); clear H16 H15 H10; intros.
repeat rewrite app_ass in H10.
simpl in H10.
exists x0; exists (@nil nat); exists (x1 ++ (x4 + x5 + 2, free) :: x6); exists x3.
Resolve_topsy.
right; right.
Resolve_topsy.
exists (x4 + x5 + 2).
Resolve_topsy.
apply In_hl_or_app; right.
simpl.
repeat rewrite get_endl_app; simpl.
repeat rewrite get_endl_app in H13; simpl in H13.
rewrite <- H13.
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
Eval_b_hyp H12.
Eval_b_goal.
OmegaZ.

(* nptr <- var_e stts; *)

  Step (

    fun (s : store.s) (h : heap.h) =>
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e result) s = eval null s /\
      exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
        (
          (exists l1,
            exists l,
              exists l2,
                exists free_size,
                  Heap_List (l1 ++ (free_size,free)::(Free_block_list l) ++ l2) adr s h /\
                  Free_block_compact_size (free_size::l) >= size /\
                (
                  (cur_adr > 0 /\ 
                    exists cur_size,
                      In_hl l1 (cur_adr, cur_size, free) adr /\
                      (s |b= var_e nptr == nat_e (cur_adr + 2 + cur_size))
                  ) \/
                  (cur_adr > 0 /\ cur_adr = get_endl l1 adr /\
                    (s |b= var_e nptr == nat_e (cur_adr + 2 + free_size))
                  ) \/
                  (l = nil /\ cur_adr > 0 /\
                    exists cur_size, 
                      In_hl l2 (cur_adr, cur_size, free) (get_endl (l1++(free_size,free)::nil) adr) /\
                      (s |b= var_e nptr == nat_e (cur_adr + 2 + cur_size))
                  )
                )
          )
        )
  ).

  red.
  Decompose_hyp.
  Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).  
  exists x.
  Resolve_topsy.
  exists x0; exists x1; exists x2; exists x3.
  Resolve_topsy.
  inversion_clear H8; Decompose_hyp.
  left.
  Resolve_topsy.
  exists x4.
  Resolve_topsy.
  inversion_clear H5; Decompose_hyp.
  right; left.
  Resolve_topsy.
  right; right.
  Resolve_topsy.
  exists x4.
  Resolve_topsy.

(* stts <-* nptr -.> status *)

(* L *)

Step TT.
red; intros.

Decompose_hyp.
unfold status.
inversion_clear H8; Decompose_hyp.

In_hl_destruct_hyp H8.
destruct x6.
exists (hlstat_bool2expr free).
apply cell_read.
split.
Hl_getstatus H1 x3.
clear H16.
rewrite get_endl_app in H13; simpl in H13.
rewrite <- H11 in H9.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists x5; exists (x3::x1); exists x2.
exists x4.
simpl Free_block_list.
Cutrewrite_hyp H1 ((x5 ++ (x4, free) :: nil) ++ (x3, free) :: Free_block_list x1 ++ x2 = x5 ++ (x4, free) :: ((x3, true) :: Free_block_list x1) ++ x2).
List_eq.
Resolve_topsy.
unfold Free_block_compact_size in H7; unfold Free_block_compact_size; simpl; simpl in H7.
omega.
right; left.
Resolve_topsy.
right; left.
Resolve_topsy.
red; intros; discriminate.
exists x3; exists x1.
Resolve_topsy.
destruct p.
exists (hlstat_bool2expr b).
apply cell_read.
split.
Hl_getstatus H1 n.
clear H16.
rewrite get_endl_app in H13; simpl in H13.
rewrite <- H11 in H9.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists (x5 ++ (x4, free) :: (n, b) :: x6); exists x1; exists x2; exists x3.
Resolve_topsy.
left.
Resolve_topsy.
exists x4.
Resolve_topsy.
left.
exists b; exists n.
Resolve_topsy.
apply In_hl_or_app.
right.
simpl.
destruct (beq_nat (get_endl x5 adr) (x + 2 + x4) && bool_eq b free && beq_nat x4 n); simpl; auto.
rewrite H11; repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
destruct b; rewrite <- expr_b_store_update_rewrite; auto.

inversion_clear H5; Decompose_hyp.
destruct x1.
simpl in H1.
destruct x2.
exists (hlstat_bool2expr alloc).
apply cell_read.
split.
Hl_getstat' H1.
rewrite get_endl_app in H12; clear H15; simpl in H12.
rewrite H9 in H10.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists x0; exists (@nil nat); exists (@nil (nat * bool)); exists x3.
Resolve_topsy.
right; left.
Resolve_topsy.
right; right.
Resolve_topsy.
rewrite get_endl_app; simpl; omega.

destruct p.
exists (hlstat_bool2expr b).
apply cell_read.
split.
Hl_getstatus H1 n.
clear H15.
rewrite get_endl_app in H12; simpl in H12.
rewrite H9 in H10.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists x0; exists (@nil nat); exists ((n,b)::x2); exists x3.
Resolve_topsy.
right; left.
Resolve_topsy.
left.
Resolve_topsy.
exists b; exists n.
Resolve_topsy.
simpl.
rewrite get_endl_app; simpl.
rewrite H9; repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
destruct b; rewrite <- expr_b_store_update_rewrite; auto.

simpl in H1.
exists (hlstat_bool2expr free).
apply cell_read.
split.
Hl_getstatus H1 n.
clear H15.
rewrite get_endl_app in H12; simpl in H12.
rewrite H9 in H10; Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists x0; exists (n::x1); exists x2; exists x3.
Resolve_topsy.
right; left.
Resolve_topsy.
right; left.
Resolve_topsy.
red; intros; discriminate.
exists n; exists x1.
Resolve_topsy.

subst x1; simpl in H1.
In_hl_destruct_hyp H8.
destruct x5.
exists (hlstat_bool2expr alloc).
apply cell_read.
split.
Hl_getstat' H1.
clear H16.
repeat rewrite get_endl_app in H13; simpl in H13.
repeat rewrite get_endl_app in H13; simpl in H13.
repeat rewrite get_endl_app in H11; simpl in H11.
rewrite <- H11 in H10; Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists x0; exists (@nil nat); exists (x1 ++ (x4,free)::nil); exists x3.
Resolve_topsy.
right; right.
Resolve_topsy.
exists x4.
Resolve_topsy.
right.
split.
rewrite <- H11.
repeat rewrite get_endl_app; simpl; repeat rewrite get_endl_app; auto.
rewrite <- expr_b_store_update_rewrite; auto.

destruct p.
exists (hlstat_bool2expr b).
apply cell_read.
split.
Hl_getstatus H1 n.
clear H16.
do 2 (rewrite get_endl_app in H13; simpl in H13).
(rewrite get_endl_app in H11; simpl in H11).
rewrite H11 in H13.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).
exists x.
Resolve_topsy.
exists x0; exists (@nil nat); exists (x1 ++ (x4,free)::(n,b)::x5); exists x3.
Resolve_topsy.
right; right.
Resolve_topsy.
exists x4.
Resolve_topsy.
left.
exists b; exists n.
split.
eapply In_hl_or_app; right; simpl.
destruct (beq_nat (get_endl x1 (get_endl (x0 ++ (x3, free) :: nil) adr)) (x + 2 + x4) && bool_eq b free && beq_nat x4 n); simpl; auto.
rewrite H11; repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
destruct b; rewrite <- expr_b_store_update_rewrite; auto.


(* Second loop QW *)

red; intros.
Decompose_hyp.
Resolve_topsy.
exists x.
Resolve_topsy.
exists x0; exists x1; exists x2; exists x3.
Resolve_topsy.
inversion_clear H9; Decompose_hyp.
inversion_clear H12; Decompose_hyp.
left.
Resolve_topsy.
exists x4; exists free; Resolve_topsy.
Omega_exprb_contradiction.
inversion_clear H6; Decompose_hyp.
inversion_clear H12; Decompose_hyp.
right; left; Resolve_topsy.
inversion_clear H7; Decompose_hyp.
Omega_exprb_contradiction.
right; left; Resolve_topsy.
inversion_clear H13; Decompose_hyp.
right; right; left.
Resolve_topsy.
exists x4; exists free; Resolve_topsy.
right; right; left.
Resolve_topsy.
exists x4; exists free; Resolve_topsy.

(* skip *)
Step TT.
red; intros.
Decompose_hyp.
Resolve_topsy.
exists x.
Resolve_topsy.
exists x0; exists x1; exists x2; exists x3.
Resolve_topsy.
inversion_clear H9; Decompose_hyp.
left.
Resolve_topsy.
exists x4; exists x5; auto.
inversion_clear H6; Decompose_hyp.
Omega_exprb_contradiction.
inversion_clear H7; Decompose_hyp.
right; right; left.
Resolve_topsy.
exists x4; exists x5; auto.
right; right; right.
Resolve_topsy.

(* cptr <-* cptr -.> next *)

Step TT.
red; intros.
Decompose_hyp.
unfold next.
inversion_clear H8; Decompose_hyp.

exists (nat_e (x + 2 + x4)).
apply cell_read.
split.
In_hl_destruct_hyp H8.
Hl_getnext H1 x4.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).  
exists (x + 2 + x4).
Resolve_topsy.
exists x0; exists x1; exists x2; exists x3.
Resolve_topsy.
In_hl_destruct_hyp H8.
destruct x7.
right; left.
Resolve_topsy.
omega.
rewrite get_endl_app.
simpl.
omega.
destruct p.
left.
Resolve_topsy.
omega.
exists n; exists b.
apply In_hl_or_app.
right; simpl.
destruct (beq_nat (get_endl x6 adr) (x + 2 + x4) && bool_eq b x5 && beq_nat x4 n); simpl; auto.
rewrite H10.
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.

inversion_clear H5; Decompose_hyp.
subst x1; simpl in H1.
exists (nat_e (x + 2 + x3)).
apply cell_read.
split.
Hl_getnext H1 x3.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).  
exists (x + 2 + x3).
Resolve_topsy.
exists x0; exists (@nil nat); exists x2; exists x3.
Resolve_topsy.
destruct x2.
right; right; right; left.
Resolve_topsy.
omega.
rewrite get_endl_app; simpl; omega.
destruct p.
right; right; left.
Resolve_topsy.
omega.
exists n; exists b.
simpl.
rewrite get_endl_app; simpl.
rewrite H9.
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.

inversion_clear H6; Decompose_hyp.

subst x1; simpl in H1.
exists (nat_e (x + 2 + x4)).
apply cell_read.
split.
In_hl_destruct_hyp H8.
Hl_getnext H1 x4.
rewrite get_endl_app in H12; simpl in H12.
rewrite get_endl_app in H10; simpl in H10.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).  
exists (x + 2 + x4).
Resolve_topsy.
exists x0; exists (@nil nat); exists x2; exists x3.
Resolve_topsy.
In_hl_destruct_hyp H8.
destruct x6.
right; right; right; left.
Resolve_topsy.
omega.
rewrite <- H10.
repeat rewrite get_endl_app; simpl.
repeat rewrite get_endl_app; auto.
destruct p.
right; right; left.
Resolve_topsy.
omega.
exists n; exists b.
apply In_hl_or_app.
right; simpl.
destruct (beq_nat (get_endl x1 (get_endl (x0 ++ (x3, free) :: nil) adr)) (x + 2 + x4) && bool_eq b x5 && beq_nat x4 n); simpl; auto.
rewrite H10.
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.

subst x1; simpl in H1.
exists (nat_e 0).
apply cell_read.
split.
Hl_getnext' H1.
repeat rewrite get_endl_app in H11; simpl in H11.
repeat rewrite get_endl_app in H10; simpl in H10.
Mapsto.
red.
Resolve_topsy; (rewrite <- expr_store_update_rewrite; auto).  
exists 0.
Resolve_topsy.
exists x0; exists (@nil nat); exists x2; exists x3.
Resolve_topsy.
tauto.

(* First loop QW *)

red; intros.
Decompose_hyp.
exists (x0 ++ (x3, free) :: Free_block_list x1 ++ x2).
Resolve_topsy.
inversion_clear H9.
Decompose_hyp.
Omega_exprb_contradiction.
inversion_clear H6.
Decompose_hyp.
Omega_exprb_contradiction.
inversion_clear H7.
Decompose_hyp.
Omega_exprb_contradiction.
inversion_clear H6.
Decompose_hyp.
Omega_exprb_contradiction.
Decompose_hyp.
subst x1.
exists (get_endl x0 adr).
exists x3.
Resolve_topsy.
unfold Free_block_compact_size in H8; simpl in H8.
omega.
apply In_hl_or_app.
right.
simpl.
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
Qed.


  (* the second call to findFree will always find a free enough block *)

Definition findFree_specif2' := forall adr size,
  size > 0 ->
  adr > 0 ->
  {{fun (s : store.s) (h : heap.h) =>
    exists l,
      Heap_List l adr s h /\
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e result) s = eval null s /\
      (exists free_adr : loc,
        (exists free_size : nat,
          free_size >= size /\ In_hl l (free_adr, free_size, free) adr))}}
    findFree size entry fnd sz stts
    {{fun (s : store.s) (h : heap.h) =>
      exists l,
        Heap_List l adr s h /\
        eval (var_e hmStart) s = eval (nat_e adr) s /\
        eval (var_e result) s = eval null s /\
        (exists finded_free_block : loc,
          (exists size'' : nat,
            size'' >= size /\
            In_hl l (finded_free_block, size'', free) adr /\
            eval (var_e entry) s = Z_of_nat finded_free_block /\
            finded_free_block > 0))}}.


Lemma findFree_verif2': findFree_specif2'.
red; intros.
unfold findFree.

Step (

fun (s : store.s) (h : heap.h) =>
    exists l1,
      exists l2,        
        exists free_size : nat,
          free_size >= size /\
          Heap_List (l1 ++ (free_size, free)::l2) adr s h /\
          eval (var_e hmStart) s = eval (nat_e adr) s /\
          eval (var_e result) s = eval null s /\
          eval (var_e entry) s = eval (nat_e adr) s
).

Decompose_hyp.
red.
In_hl_destruct_hyp H6.
exists x2; exists x3; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).

Step (

fun (s : store.s) (h : heap.h) =>
    exists l1,
      exists l2,        
        exists free_size : nat,
          free_size >= size /\
          Heap_List (l1 ++ (free_size, free)::l2) adr s h /\
          eval (var_e hmStart) s = eval (nat_e adr) s /\
          eval (var_e result) s = eval null s /\
          eval (var_e entry) s = eval (nat_e adr) s             
).

Decompose_hyp.
unfold status.
destruct x.
simpl in H4.
exists (hlstat_bool2expr free).
apply cell_read.
split.
Hl_getstatus H4 x1.
simpl in H9.
Mapsto.
red.
exists (@nil (nat * bool)); exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
destruct p.
exists (hlstat_bool2expr b).
apply cell_read.
split.
Hl_getstatus H4 n.
simpl in H9.
Mapsto.
red.
exists ((n,b)::x); exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).

Step (
  fun (s : store.s) (h : heap.h) =>
    exists l1,
      exists l2,        
        exists free_size : nat,
          free_size >= size /\
          Heap_List (l1 ++ (free_size, free)::l2) adr s h /\
          eval (var_e hmStart) s = eval (nat_e adr) s /\
          eval (var_e result) s = eval null s /\
          eval (var_e entry) s = eval (nat_e adr) s /\
          eval (var_e fnd) s = eval (nat_e 0) s
).

red.
Decompose_hyp.
exists x; exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).

Step (

  fun (s : store.s) (h : heap.h) =>
    exists l1,
      exists l2,        
        exists free_size : nat,
          free_size >= size /\
          Heap_List (l1 ++ (free_size, free)::l2) adr s h /\
          eval (var_e hmStart) s = eval (nat_e adr) s /\
          eval (var_e result) s = eval null s /\
          exists cur_adr,
            eval (var_e entry) s = eval (nat_e cur_adr) s /\
            (
              (exists cur_size, 
                exists cur_status,
                  In_hl l1 (cur_adr,cur_size,cur_status) adr /\
                  (
                    (
                      eval (var_e fnd) s = eval (nat_e 0) s
                    ) \/
                    (
                      eval (var_e fnd) s = eval (nat_e 1) s /\
                      cur_size >= size /\
                      cur_status = free
                    )
                  )                  
              ) \/
              (
                cur_adr = get_endl l1 adr
              ) 
            )
).

red; intros.
Decompose_hyp.
exists x; exists x0; exists x1.
Resolve_topsy.
exists adr.
Resolve_topsy.
destruct x.
right.
auto.
destruct p.
left.
exists n; exists b.
Resolve_topsy.
simpl.
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.

Step (

  fun (s : store.s) (h : heap.h) =>
    exists l1,
      exists l2,        
        exists free_size : nat,
          free_size >= size /\
          Heap_List (l1 ++ (free_size, free)::l2) adr s h /\
          eval (var_e hmStart) s = eval (nat_e adr) s /\
          eval (var_e result) s = eval null s /\
          exists cur_adr,
            eval (var_e entry) s = eval (nat_e cur_adr) s /\
            (
              (exists cur_size, 
                exists cur_status,
                  In_hl l1 (cur_adr,cur_size,cur_status) adr /\
                  eval (var_e fnd) s = eval (nat_e 0) s /\
                  eval (var_e stts) s = eval (hlstat_bool2expr cur_status) s
              ) \/
              (
                cur_adr = get_endl l1 adr /\
                eval (var_e stts) s = eval (hlstat_bool2expr free) s
              ) 
            )
).

Decompose_hyp.
inversion_clear H8; Decompose_hyp.
inversion_clear H9; Decompose_hyp.
unfold status.
exists (hlstat_bool2expr x4).
apply cell_read.
split.
In_hl_destruct_hyp H8.
Hl_getstatus H5 x3.
Mapsto.
red.
exists x; exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists x2.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
left.
exists x3; exists x4.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
destruct x4; try (rewrite <- expr_store_update_rewrite; auto).
generalize (In_hl_ge_start _ _ _ _ _ H8); Omega_exprb_contradiction.
unfold status.
exists (hlstat_bool2expr free).
apply cell_read; split.
Hl_getstatus H5 x1.
Mapsto.
red.
exists x; exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists x2.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
right.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).

Step (

  fun (s : store.s) (h : heap.h) =>
    exists l1,
      exists l2,        
        exists free_size : nat,
          free_size >= size /\
          Heap_List (l1 ++ (free_size, free)::l2) adr s h /\
          eval (var_e hmStart) s = eval (nat_e adr) s /\
          eval (var_e result) s = eval null s /\
          exists cur_adr,
            eval (var_e entry) s = eval (nat_e cur_adr) s /\
            (
              (exists cur_size, 
                exists cur_status,
                  In_hl l1 (cur_adr,cur_size,cur_status) adr /\
                  eval (var_e fnd) s = eval (nat_e 0) s /\
                  eval (var_e stts) s = eval (hlstat_bool2expr cur_status) s /\                 
                  eval (var_e sz) s = eval (nat_e cur_size) s
              ) \/
              (
                cur_adr = get_endl l1 adr  /\
                eval (var_e stts) s = eval (hlstat_bool2expr free) s /\
                eval (var_e sz) s = eval (nat_e free_size) s
              ) 
            )

).

unfold ENTRYSIZE.

Step (

  fun (s : store.s) (h : heap.h) =>
    exists l1,
      exists l2,        
        exists free_size : nat,
          free_size >= size /\
          Heap_List (l1 ++ (free_size, free)::l2) adr s h /\
          eval (var_e hmStart) s = eval (nat_e adr) s /\
          eval (var_e result) s = eval null s /\
          exists cur_adr,
            eval (var_e entry) s = eval (nat_e cur_adr) s /\
            (
              (exists cur_size, 
                exists cur_status,
                  In_hl l1 (cur_adr,cur_size,cur_status) adr /\
                  eval (var_e fnd) s = eval (nat_e 0) s /\
                  eval (var_e stts) s = eval (hlstat_bool2expr cur_status) s /\
                  eval (var_e sz) s = eval (nat_e (cur_adr + 2 + cur_size)) s                  
              ) \/
              (
                cur_adr = get_endl l1 adr /\
                eval (var_e stts) s = eval (hlstat_bool2expr free) s /\
                eval (var_e sz) s = eval (nat_e (cur_adr + 2 + free_size)) s                  
              ) 
            )
).

Decompose_hyp.
unfold next.
inversion_clear H7; Decompose_hyp.
exists (nat_e (x2 + 2 + x3)).
apply cell_read.
split.
In_hl_destruct_hyp H7.
Hl_getnext H4 x3.
Mapsto.
red.
exists x; exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists x2.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
left.
exists x3; exists x4.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
destruct x4; try (rewrite <- expr_store_update_rewrite; auto).
exists (nat_e (x2 + 2 + x1)).
apply cell_read.
split.
Hl_getnext H4 x1.
Mapsto.
red.
exists x; exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists x2.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
right.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).

Step (

  fun (s : store.s) (h : heap.h) =>
    exists l1,
      exists l2,        
        exists free_size : nat,
          free_size >= size /\
          Heap_List (l1 ++ (free_size, free)::l2) adr s h /\
          eval (var_e hmStart) s = eval (nat_e adr) s /\
          eval (var_e result) s = eval null s /\
          exists cur_adr,
            eval (var_e entry) s = eval (nat_e cur_adr) s /\
            (
              (exists cur_size, 
                exists cur_status,
                  In_hl l1 (cur_adr,cur_size,cur_status) adr /\
                  eval (var_e fnd) s = eval (nat_e 0) s /\
                  eval (var_e stts) s = eval (hlstat_bool2expr cur_status) s /\
                  eval (var_e sz) s = eval (nat_e cur_size) s                  
              ) \/
              (
                cur_adr = get_endl l1 adr /\
                eval (var_e stts) s = eval (hlstat_bool2expr free) s /\
                eval (var_e sz) s = eval (nat_e free_size) s                  
              ) 
            )
).

Decompose_hyp.
inversion_clear H7; Decompose_hyp.
red.
exists x; exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists x2.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
left.
exists x3; exists x4.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
destruct x4; try (rewrite <- expr_store_update_rewrite; auto).
rewrite <- expr_store_update_rewrite.
simpl.
simpl in H11.
simpl in H6.
OmegaZ.
red.
exists x; exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists x2.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
right.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
rewrite <- expr_store_update_rewrite.
simpl.
simpl in H10.
simpl in H6.
OmegaZ.

Step TT.

Step TT.

intros.
Decompose_hyp.
inversion_clear H8; Decompose_hyp.
Omega_exprb_contradiction. 
Omega_exprb_contradiction. 

Step TT.

red; intros.
intuition.

Step TT.

Step TT.

intros.
Decompose_hyp.
inversion_clear H8; Decompose_hyp.
red.
exists x; exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists x2.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
left.
exists x3; exists x4.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
right.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
Omega_exprb.
destruct x4.
Omega_exprb.
Omega_exprb_contradiction.

red.
exists x; exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists x2.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).

Step TT.
red; intros.
unfold next.
Decompose_hyp.
inversion_clear H8; Decompose_hyp.
exists (nat_e (x2 + 2 + x3)).
apply cell_read.
split.
In_hl_destruct_hyp H8.
Hl_getnext H5 x3.
Mapsto.
red.
exists x; exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists (x2 + 2 + x3).
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
In_hl_destruct_hyp H8.
destruct x6.
repeat rewrite app_ass in H5; simpl in H5.
right.
rewrite get_endl_app; simpl; auto.
destruct p.
left.
exists n; exists b.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
apply In_hl_or_app; right.
simpl.
destruct (beq_nat (get_endl x5 adr) (x2 + 2 + x3) && bool_eq b x4 && beq_nat x3 n); auto.
rewrite H13.
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
Omega_exprb_contradiction.

red; intros.
Decompose_hyp.
inversion_clear H8; Decompose_hyp.
inversion_clear H9.
simpl in H1.
generalize (In_hl_ge_start _ _ _ _ _ H8); intros.
Omega_exprb_contradiction.
Decompose_hyp.
exists (x ++ (x1, free) :: x0).
Resolve_topsy.
exists x2.
exists x3.
Resolve_topsy.
subst x4.
apply In_hl_or_app; left; auto.
generalize (In_hl_ge_start _ _ _ _ _ H8); intros.
omega.
exists (x ++ (x1, free) :: x0).
Resolve_topsy.
exists (get_endl x adr).
exists x1.
Resolve_topsy.
apply In_hl_or_app; right; simpl.
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
Omega_exprb.
generalize (get_endl_gt x adr); intros; omega.
Qed.

(* The splitting will be performed as usual (previous proof is reusable??) *)

Definition split_specif2 := forall adr size, 
  size > 0 ->
  adr > 0 ->
  {{fun s => fun h =>  exists l,
    Heap_List l adr s h /\ 
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\    
    (exists finded_free_block, exists size'', size'' >= size /\ 
      In_hl l (finded_free_block,size'',free) adr /\ 
      eval (var_e entry) s = (Z_of_nat finded_free_block) /\ 
      finded_free_block > 0) }}
  
  split entry size cptr sz
    
    {{fun s => fun h => exists l,
      (exists y, y > 0 /\ eval (var_e entry) s = Z_of_nat (y) /\
        (exists size'', size'' >= size /\      
          (Heap_List l adr ** Array (y+2) size'') s h /\ 
          In_hl l (y,size'', alloc) adr))}}.

Lemma split_verif2: split_specif2.
red.
intros.
unfold split.

Step (
  fun s => fun h =>  exists l,
    Heap_List l adr s h /\ 
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\    
    exists finded_free_block, exists size'', size'' >= size /\ 
      In_hl l (finded_free_block,size'',free) adr /\ 
      eval (var_e entry) s = (Z_of_nat finded_free_block) /\ 
      finded_free_block > 0 /\
      eval (var_e sz) s = eval (nat_e size'') s     
).

unfold ENTRYSIZE.

Step (
  fun s => fun h =>  exists l,
    Heap_List l adr s h /\ 
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\    
    exists finded_free_block, exists size'', size'' >= size /\ 
      In_hl l (finded_free_block,size'',free) adr /\ 
      eval (var_e entry) s = (Z_of_nat finded_free_block) /\ 
      finded_free_block > 0 /\
      eval (var_e sz) s = eval (nat_e (finded_free_block + 2 + size'')) s     
).

Decompose_hyp.
exists (nat_e (x0 + 2 + x1)).
apply cell_read.
unfold next; split.
In_hl_destruct_hyp H7.
Hl_getnext H1 x1.
Mapsto.
red.
exists x.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).

Step (
  fun s => fun h =>  exists l,
    Heap_List l adr s h /\ 
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\    
    exists finded_free_block, exists size'', size'' >= size /\ 
      In_hl l (finded_free_block,size'',free) adr /\ 
      eval (var_e entry) s = (Z_of_nat finded_free_block) /\ 
      finded_free_block > 0 /\
      eval (var_e sz) s = eval (nat_e size'') s     
).

Decompose_hyp.
red.
exists x.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
Omega_exprb.

Step TT.

Step TT.

intros.
Decompose_hyp.
Omega_exprb_contradiction.

Step TT.

red; intros.
Decompose_hyp.
exists x.
Resolve_topsy.
exists x0; exists x1.
Resolve_topsy.

Step (
  fun s => fun h =>  exists l,
    Heap_List l adr s h /\ 
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\    
    exists finded_free_block, exists size'', size'' >= size /\ 
      In_hl l (finded_free_block,size'',free) adr /\ 
      eval (var_e entry) s = (Z_of_nat finded_free_block) /\ 
      finded_free_block > 0
).

Step (
  fun s => fun h =>  exists l,
    Heap_List l adr s h /\ 
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\    
    exists finded_free_block, 
      exists size'', size'' >= size + LEFTOVER + 2 /\ 
        In_hl l (finded_free_block,size'',free) adr /\ 
        eval (var_e entry) s = (Z_of_nat finded_free_block) /\ 
        finded_free_block > 0 /\
        eval (var_e sz) s = eval (nat_e size'') s /\
        eval (var_e cptr) s = eval (nat_e (finded_free_block + 2 + size)) s 
).

Decompose_hyp.
red.
exists x.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
unfold LEFTOVER.
Omega_exprb.
Omega_exprb.

Step (
  fun s => fun h =>  exists l,
    Heap_List l adr s h /\ 
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\    
    exists finded_free_block, 
      exists size'', size'' >= size + LEFTOVER + 2 /\ 
        In_hl l (finded_free_block,size'',free) adr /\ 
        eval (var_e entry) s = (Z_of_nat finded_free_block) /\ 
        finded_free_block > 0 /\
        eval (var_e sz) s = eval (nat_e (finded_free_block + 2 + size'')) s /\
        eval (var_e cptr) s = eval (nat_e (finded_free_block + 2 + size)) s 
).

Decompose_hyp.
unfold next.
exists (nat_e (x0 + 2 + x1)).
apply cell_read.
split.
In_hl_destruct_hyp H7.
Hl_getnext H1 x1.
Mapsto.
red.
exists x.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
exists x0; exists x1; Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).

Step (fun (s : store.s) (h : heap.h) =>
  exists e'' : expr,
    ((cptr -.> status) |-> e'' **
      ((cptr -.> status) |-> Free -*
       (fun (s0 : store.s) (h0 : heap.h) =>
        exists e''0 : expr,
          ((entry -.> next) |-> e''0 **
           ((entry -.> next) |-> var_e cptr -*
            (fun (s1 : store.s) (h1 : heap.h) =>
             exists l : list (nat * bool),
               Heap_List l adr s1 h1 /\
               eval (var_e hmStart) s1 = eval (nat_e adr) s1 /\
               eval (var_e result) s1 = eval null s1 /\
               (exists finded_free_block : nat,
                  (exists size'' : nat,
                     size'' >= size /\
                     In_hl l (finded_free_block, size'', free) adr /\
                     eval (var_e entry) s1 = Z_of_nat finded_free_block /\
                     finded_free_block > 0))))) s0 h0))) s h
).

Decompose_hyp.
assert (x1 = size + 2 + (x1 - 2 - size)).
omega.
rewrite H5 in H7.
clear H5.
In_hl_destruct_hyp H7.
generalize (hl_splitting _ _ _ _ _ _ _ H1); intros; clear H1.
Decompose_hyp.
exists x.
unfold next; unfold status.
Compose_sepcon H5 H1.
Mapsto.
red; intros.
assert (H1 # h' /\ (nat_e (get_endl x2 adr + size + 3) |-> nat_e (get_endl x2 adr + size + (x1 - 2 - size) + 4)) s h').
intuition.
Mapsto.
simpl in H9.
rewrite H9.
OmegaZ.
clear H15 H13.
generalize (H16 _ H18 _ H17); clear H16 H18; intros.
Decompose_hyp.
exists x4.
Compose_sepcon H13 H15.
Mapsto.
red; intros.
assert (H15 # h'0 /\ (nat_e (get_endl x2 adr + size + 2) |-> Free) s h'0).
clear H18.
intuition.
Mapsto.
clear H18 H20.
generalize (H21 _ H23 _ H22); clear H21 H23; intros.
Decompose_hyp.
exists x5.
Compose_sepcon H18 H20.
Mapsto.
red; intros.
clear H23.
assert (H20 # h'1 /\ (nat_e (get_endl x2 adr + 1) |-> nat_e (get_endl x2 adr + size + 2)) s h'1).
intuition.
Mapsto.
clear H25.
generalize (H26 _ H23 _ H27); clear H26 H23; intros.
exists (x2 ++ (size, true) :: (x1 - 2 - size, true) :: x3).
Resolve_topsy.
exists x0; exists size.
Resolve_topsy.
apply In_hl_or_app; right; simpl.
rewrite H12.
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.

Step (
(fun (s0 : store.s) (h0 : heap.h) =>
    exists e'' : expr,
      ((entry -.> next) |-> e'' **
       ((entry -.> next) |-> var_e cptr -*
        (fun (s : store.s) (h : heap.h) =>
         exists l : list (nat * bool),
           Heap_List l adr s h /\
           eval (var_e hmStart) s = eval (nat_e adr) s /\
           eval (var_e result) s = eval null s /\
           (exists finded_free_block : nat,
              (exists size'' : nat,
                 size'' >= size /\
                 In_hl l (finded_free_block, size'', free) adr /\
                 eval (var_e entry) s = Z_of_nat finded_free_block /\
                 finded_free_block > 0))))) s0 h0)
).

auto.

Step TT.
red; intros; auto.


Step TT.
red; intros.
inversion_clear H1.
Decompose_hyp.
exists x.
Resolve_topsy.
exists x0; exists x1.
Resolve_topsy.

Step TT.

red; intros.
Decompose_hyp.
unfold status.
In_hl_destruct_hyp H7.
generalize (hl_free2alloc _ _ _ _ _ _ H1); clear H1; intros.
Decompose_hyp.
exists x.
Compose_sepcon H1 H5.
Mapsto.
clear H11.
red; intros.
assert (H5 # h' /\ ((nat_e (get_endl x2 adr) |-> Allocated)) s h').
intuition.
Mapsto.
generalize (H14 _ H15 _ H13); intros.
exists (x2 ++ (x1, false) :: x3).
exists x0.
Resolve_topsy.
exists x1.
Resolve_topsy.
Decompose_sepcon H16 h1 h2.
Compose_sepcon h1 h2.
Resolve_topsy.
Array_equiv.
apply In_hl_or_app; right.
simpl.
rewrite H10.
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
Qed.

Definition hmAlloc_specif2 := forall adr size,
  adr > 0 -> size > 0 ->
  {{ fun s h => exists l1, exists l2, exists l,  
    (Heap_List (l1 ++ (Free_block_list l) ++ l2) adr) s h /\
    Free_block_compact_size l >= size /\
    (s |b= var_e hmStart == nat_e adr) }}
  
  hmAlloc result size entry cptr fnd stts nptr sz
  
  {{ fun s h => exists l, exists y, 
    y > 0 /\ (s |b= var_e result == nat_e (y+2)) /\
    exists size'', size'' >= size /\
      (Heap_List l adr ** Array (y + 2) size'') s h /\ 
      In_hl l (y,size'',alloc) adr
  }}.


Lemma hmAlloc_verif2: hmAlloc_specif2.
  unfold hmAlloc_specif2.
  intros.
  unfold hmAlloc.
  
Step (  
  fun s h => exists l1, exists l2, exists l,  
    (Heap_List (l1 ++ (Free_block_list l) ++ l2) adr) s h /\
    Free_block_compact_size l >= size /\
    (s |b= var_e hmStart == nat_e adr) /\
    (s |b= var_e result == null)
).

red.
Decompose_hyp.
exists x; exists x0; exists x1.
Resolve_topsy.

Step (
fun s => fun h =>  exists l1, exists l2, exists l,  
    (Heap_List (l1 ++ (Free_block_list l) ++ l2) adr) s h /\
    (Free_block_compact_size l) >= size /\
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\
    (
      (exists finded_free_block, exists size'', size'' >= size /\ 
        In_hl (l1 ++ (Free_block_list l) ++ l2) (finded_free_block,size'',free) adr /\ 
        eval (var_e entry) s = (Z_of_nat finded_free_block) /\ 
        finded_free_block > 0)
      \/
      (eval (var_e entry) s = eval null s)
    )
).

generalize (findFree_verif2 adr size H0 H); intros.

Step TT.
clear H1.
red; intros.
Decompose_hyp.
exists x; exists x0; exists x1.
Resolve_topsy.
Omega_exprb. 
Omega_exprb. 
clear H1.
red; intros.
Decompose_hyp.
exists x; exists x0; exists x1.
Resolve_topsy.

Step (
  fun (s : store.s) (h : heap.h) =>
    exists l,
      Heap_List l adr s h /\
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e result) s = eval null s /\
      (exists finded_free_block : loc,
        (exists size'' : nat,
          size'' >= size /\
          In_hl l (finded_free_block, size'', free) adr /\
          eval (var_e entry) s = Z_of_nat finded_free_block /\
          finded_free_block > 0))
).

Step (
fun s => fun h =>  exists l1, exists l2, exists l,  
    (Heap_List (l1 ++ (Free_block_list l) ++ l2) adr) s h /\
    (Free_block_compact_size l) >= size /\
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\
    eval (var_e entry) s = eval null s /\
    eval (var_e cptr) s = eval (nat_e adr) s
).

Decompose_hyp.
inversion_clear H8; Decompose_hyp.
Omega_exprb_contradiction.
red.
exists x; exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).

Step (
  fun s => fun h => exists l,  
    (Heap_List l adr) s h /\
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\
    (exists free_adr, exists free_size, free_size >= size /\
      In_hl l (free_adr, free_size, free) adr
    )
).

generalize (compact_verif2 adr size H0 H); intros.

Step TT.
clear H1.
red; intros.
Decompose_hyp.
exists x; exists x0; exists x1.
Resolve_topsy; try (rewrite <- expr_store_update_rewrite; auto).
clear H1; red; intros.
auto.

generalize (findFree_verif2' adr size H0 H); intros.

Step TT.
clear H1.
red; intros.
auto.
clear H1.
red; intros.
auto.

Step TT.

red; intros.
Decompose_hyp.
inversion_clear H8; Decompose_hyp.
exists (x ++ Free_block_list x1 ++ x0).
Resolve_topsy.
exists x2; exists x3.
Resolve_topsy.
Omega_exprb_contradiction.

Step TT.

Step TT.

intros.
Decompose_hyp.
Omega_exprb_contradiction.

Step (
  fun s => fun h => exists l,
    (exists y, y > 0 /\ eval (var_e entry) s = Z_of_nat (y) /\
      (exists size'', size'' >= size /\      
        (Heap_List l adr ** Array (y+2) size'') s h /\ 
        In_hl l (y,size'', alloc) adr))
).

generalize (split_verif2 _ _ H0 H); intros.

Step TT.
clear H1.
red; intros.
Decompose_hyp.
exists x.
Resolve_topsy.
exists x0; exists x1.
Resolve_topsy.
clear H1.
red; intros; auto.

Step TT.
intros.
Decompose_hyp.
red; exists x; Resolve_topsy.
exists x0; Resolve_topsy.
exists x1; Resolve_topsy.
Compose_sepcon H1 H5.
Resolve_topsy.
Array_equiv.
Qed.



