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
Require Import topsy_hm_old.
Require Import topsy_hmAlloc_old.

Print Free.

Fixpoint compact' (l:list (loc * nat *  expr)) (len:nat) {struct len} : list (loc * nat *  expr) :=
  match len with
    O => nil
    | S len' =>
      match l with
	nil => nil
	| (adr, sz, st)::tl => match (expr_eq Allocated st) with
                                          true => (adr, sz, Allocated)::(compact' tl len')
                                          | false =>
                                                match tl with
                                                    nil => (adr, sz, Free)::nil
                                                    | (adr',sz',st')::tl' => match (expr_eq Allocated st) with
                                                                                       true => (adr, sz, Allocated)::(compact' tl len')
                                                                                       | false => compact' ((adr, sz+sz'+2, Free)::tl) len'
                                                                                    end
                                                end
                                       end
      end
  end.

Definition  compact_coq_fct (l:list (loc * nat *  expr)): list (loc * nat *  expr) := compact' l (length l).

Inductive compact_coq_ind: (list (nat * loc * expr)) -> (list (nat * loc * expr)) -> Prop :=
    compact_coq_ind_nil: compact_coq_ind nil nil
    | compact_coq_ind_Alloc: forall adr size l l',
                         compact_coq_ind l l' ->
                         compact_coq_ind ((adr, size, Allocated)::l) ((adr, size, Allocated)::l')                         
    | compact_coq_ind_last_Free: forall adr size,
                         compact_coq_ind ((adr, size, Free)::nil) ((adr, size, Free)::nil)                         
    | compact_coq_ind_Free_Free: forall adr size adr' size' l l',
                         compact_coq_ind ((adr,size + 2 + size', Free)::l) l' ->
                         compact_coq_ind ((adr,size, Free)::(adr',size', Free)::l) l'
    | compact_coq_ind_Free_Alloc: forall adr size adr' size' l l',
                         compact_coq_ind l l' ->
                         compact_coq_ind ((adr,size, Free)::(adr',size', Allocated)::l) ((adr,size, Free)::(adr',size', Allocated)::l').

Axiom compact_coq_ind2fct: forall l s h startl,
               Heap_List l startl 0 s h ->
               (forall l', compact_coq_fct l = l' <-> compact_coq_ind l l').

Inductive split_coq_ind: (list (nat * loc * expr)) -> nat -> loc -> (list (nat * loc * expr)) -> Prop :=
    split_coq_ind_nil: forall n sz, split_coq_ind nil sz n nil
    | split_coq_ind_Alloc: forall adr sz n size l l',
                          split_coq_ind l size n l' ->
                          split_coq_ind ((adr,sz,Allocated)::l) size n ((adr,sz,Allocated)::l')
    | split_coq_ind_Free: forall adr sz l l' n size,
                       adr <> n ->
                       split_coq_ind l size n l' ->
                       split_coq_ind ((adr,sz,Allocated)::l) size n ((adr,sz,Allocated)::l')
    | split_coq_ind_Free_split: forall adr sz l n size,
                       adr = n ->
                       sz >= size + LEFTOVER + 2 ->
                       split_coq_ind ((adr,sz,Free)::l) size n ((adr,size,Free)::(adr+2+size,sz-2-size,Free)::l)
    | split_coq_ind_Free_split': forall adr sz l n size,
                       adr = n ->
                       sz < size + LEFTOVER + 2 ->
                       split_coq_ind ((adr,sz,Free)::l) size n ((adr,sz,Free)::l).
              
Inductive freeblocks': list (nat * loc * expr) -> Z -> Prop :=
    freeblocks'_nil: freeblocks' nil 0%Z
    | freeblocks'_Allocated: forall adr sz l l' n,
                    freeblocks' l n ->
                    freeblocks' (l' ++ (adr,sz,Allocated)::l) n
    | freeblocks'_Free_end: forall adr sz l,
                    freeblocks' ((adr,sz,Allocated)::l) 0%Z
    | freeblocks'_Free_suiv: forall adr sz l n,
                    freeblocks' l (n - (Z_of_nat sz) - 2)%Z ->
                    freeblocks' ((adr,sz,Free)::l) n.

Definition freeblocks (l: list (nat * loc * expr)) (n: nat) :=
                    freeblocks' l (Z_of_nat (n + 2)).

Inductive freeblock': list (loc * nat * expr) -> nat -> Prop :=
  freeblock'_nil: freeblock' nil 0
  | freeblock'_free : forall adr sz l n, 
    freeblock' l n ->
    freeblock' ((adr,sz,Free)::l) (n+sz).

Definition freeblock (l: list (loc * nat * expr)) (n: nat):= 
     exists l1, exists l2, exists l', l = (l1 ++ l' ++ l2) /\ freeblock' l' n.

Definition hmAlloc_specif3 := forall l result adr size entry cptr fnd stts nptr sz, 
  (var.set (hmStart::result::entry::cptr::fnd::stts::nptr::sz::nil)) -> 
  adr > 0 -> size > 0 ->

  {{fun s h =>  Heap_List l adr 0 s h /\
        eval (var_e hmStart) s = eval (nat_e adr) s /\
        exists free_size, freeblocks l free_size /\ free_size >= size
        }}
  
  hmAlloc result size entry cptr fnd stts nptr sz
  
  {{ fun s => fun h => 
      exists l', 
      exists y, y > 0 /\ eval (var_e result) s = Z_of_nat (y+2) /\
      exists size'', size'' >= size /\
      (Heap_List l adr 0 ** Array (y + 2) size'') s h /\ 
      In (y,size'',Allocated) l /\ 
      (
        (exists l'', compact_coq_ind l l'' /\ split_coq_ind l'' size y l')
        \/
        (split_coq_ind l size y l')
      )
}}.


(*
debut de preuve pour 
compact_coq_ind2fct

induction l.
intros.
split; intros.
unfold compact_coq_fct in H0.
simpl in H0.
subst l'.
apply compact_coq_ind_nil.
inversion H0.
subst l'.
auto.
destruct a as [X st].
destruct X as [adr sz].
intros.
destruct l.
assert (st = Allocated \/ st = Free).
apply (Heap_List_block_status' ((adr,sz,st)::nil) adr sz st _ _ _ _ H); intros.
intuition.
split; intros.

inversion_clear H0.
subst st.
unfold compact_coq_fct in H1.
simpl in H1.
subst l'.
eapply compact_coq_ind_Alloc.
eapply compact_coq_ind_nil.
subst st.
unfold compact_coq_fct in H1.
simpl in H1.
subst l'.
eapply compact_coq_ind_last_Free.
inversion_clear H0.
subst st.
inversion_clear H1.
unfold compact_coq_fct.
simpl.
inversion_clear H0.
auto.
subst st.
inversion_clear H1.
unfold compact_coq_fct.
simpl.
auto.

destruct p as [X st'].
destruct X as [adr' sz'].
assert (adr' = adr + 2 + sz).
eapply Heap_List_next_bloc with (l1 := hl_nil).
simpl.
apply H.
subst adr'.
assert (st = Allocated \/ st = Free).
apply (Heap_List_block_status' _ adr sz st _ _ _ _ H); intros.
intuition.
assert (st' = Allocated \/ st' = Free).
apply (Heap_List_block_status' _ (adr + 2 + sz) sz' st' _ _ _ _ H); intros.
intuition.
inversion_clear H0.
inversion_clear H1.
subst st st'.
split; intros.
unfold compact_coq_fct in H0.
simpl in H0.
rewrite <- H0.
eapply compact_coq_ind_Alloc.
eapply compact_coq_ind_Alloc.

unfold compact_coq_fct in H0.
simpl in H0.
subst l'.
*)

(* a generale specification *)
Definition findFree_specif := forall adr entry fnd sz stts size sizex x result l,
    size > 0 ->
    sizex > 0 ->
    adr > 0 ->
    var.set (hmStart::entry::fnd::sz::stts::result::nil) ->

    {{fun s => fun h => Heap_List l adr 0 s h /\ 
    In (x,sizex,Allocated) l /\
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s }}

    findFree size entry fnd sz stts

    {{fun s => fun h => 
    Heap_List l adr 0 s h /\ 
    In (x,sizex,Allocated) l /\
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\    
    (
    (exists finded_free_block, exists size'', size'' >= size /\ 
     In (finded_free_block,size'',Free) l /\ 
     eval (var_e entry) s = (Z_of_nat finded_free_block) /\ 
     finded_free_block > 0)
    \/
    (eval (var_e entry) s = eval null s)
    )}}.


Lemma findFree_verif : findFree_specif.
unfold findFree_specif.
intros.
unfold findFree.

Step (

fun (s : store.s) (h : heap.h) =>
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       eval (var_e entry) s = eval (nat_e adr) s

).

decompose [and] H3; clear H3.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
Store_update.

Step (

fun (s : store.s) (h : heap.h) =>
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       eval (var_e entry) s = eval (nat_e adr) s /\
       (eval (var_e stts) s = eval Allocated s \/ eval (var_e stts) s = eval Free s)
       
).

decompose [and] H3; clear H3.
induction l.
simpl in H6; contradiction.
clear IHl.
induction a as [X bloc_status].
induction X as [bloc_adr bloc_size].
assert (In (bloc_adr, bloc_size, bloc_status) ((bloc_adr, bloc_size, bloc_status) :: l)).
auto with *.
eapply Heap_List_status.
apply H3.
Compose_sepcon h heap.emp.
apply H4.
red; auto.
generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H4); intros.
unfold status.
Simpl_eval.
Omega_exprb.

red.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
split.
Store_update.
generalize (Heap_List_block_status _ _ _ _ _ _ _ H4 H3); intros.
inversion_clear H8.
subst bloc_status.
Store_update.
subst bloc_status.
Store_update.


Step (

fun (s : store.s) (h : heap.h) =>
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       eval (var_e entry) s = eval (nat_e adr) s /\
       (eval (var_e stts) s = eval Allocated s \/ eval (var_e stts) s = eval Free s) /\
       eval (var_e fnd) s = eval (nat_e 0) s
       
).

red.
decompose [and] H3; clear H3.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
Store_update.

Step (

fun (s : store.s) (h : heap.h) =>
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       (exists bloc_adr, 
         eval (var_e entry) s = eval (nat_e bloc_adr) s /\
         (
           (bloc_adr = 0 /\ eval (var_e fnd) s = eval (nat_e 0) s) \/
           ((Heap_List l adr bloc_adr ** Heap_List nil bloc_adr 0) s h /\
            eval (var_e fnd) s = eval (nat_e 0) s /\
            bloc_adr > 0) \/
           (exists bloc_size, exists bloc_status,
            bloc_adr > 0 /\
            In (bloc_adr, bloc_size, bloc_status) l /\ 
            eval (var_e fnd) s = eval (nat_e 0) s
           ) \/
           (exists bloc_size, bloc_size >= size /\
            In (bloc_adr, bloc_size, Free) l /\ 
            eval (var_e fnd) s = eval (nat_e 1) s /\
            bloc_adr >0
           ) 
         )         
       )      
       
).

red; intros.
decompose [and] H3; clear H3.
split; auto.
split; auto.
split; auto.
split; auto.
exists adr.
split; auto.
right.
right.
left.
induction l.
simpl in H6; contradiction.
clear IHl.
induction a as [X bloc_status].
induction X as [bloc_adr bloc_size].
generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H4); intros.
subst adr.
exists bloc_size.
exists bloc_status.
split; auto.
split.
auto with *.
auto.

Step (

fun (s : store.s) (h : heap.h) =>
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       (exists bloc_adr, 
         eval (var_e entry) s = eval (nat_e bloc_adr) s /\
         (
           ((Heap_List l adr bloc_adr ** Heap_List nil bloc_adr 0) s h /\
            eval (var_e fnd) s = eval (nat_e 0) s /\
            eval (var_e stts) s = eval Allocated s /\
            bloc_adr > 0) \/
           (exists bloc_size, exists bloc_status, 
            In (bloc_adr, bloc_size, bloc_status) l /\ 
            eval (var_e fnd) s = eval (nat_e 0) s /\
            (eval (var_e stts) s = eval bloc_status s) /\
            bloc_adr > 0
           )
         )         
       )      
       
).
inversion_clear H3.
decompose [and] H4; clear H4.
inversion_clear H10 as [bloc_adr].
inversion_clear H4.

inversion_clear H10.

inversion_clear H4.
assert (bloc_adr <> 0).
Simpl_eval.
Omega_exprb.
contradiction.

inversion_clear H4.
decompose [and] H10; clear H10.
eapply Heap_List_status_last.
apply H13.
Decompose_sepcon H4 h1 h2.
Compose_sepcon h2 h1.
auto.
red; auto.
unfold status.
Simpl_eval.
Omega_exprb.
red.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists bloc_adr.
split.
Store_update.
left.
split.
Decompose_sepcon H4 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Heap_List_equiv.
split.
Store_update.
Store_update.

inversion_clear H10.
inversion_clear H4 as [bloc_size].
inversion_clear H10 as [bloc_status].
decompose [and] H4; clear H4.

eapply Heap_List_status.
apply H12.
Compose_sepcon h heap.emp.
apply H3.
red; auto.
unfold status.
Simpl_eval.
Omega_exprb.
red.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists bloc_adr.
split.
Store_update.
right.
exists bloc_size.
exists bloc_status.
split; auto.
split.
Store_update.
generalize (Heap_List_block_status _ _ _ _ _ _ _ H3 H12); intro X; inversion_clear X.
subst bloc_status.
Store_update.
subst bloc_status.
Store_update.

inversion_clear H4 as [bloc_size].
decompose [and] H10; clear H10.
assert (eval (var_e fnd) s <> eval (nat_e 1) s).
Omega_exprb.
contradiction.

Step (

fun (s : store.s) (h : heap.h) =>
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       (exists bloc_adr, 
         eval (var_e entry) s = eval (nat_e bloc_adr) s /\
         (
           ((Heap_List l adr bloc_adr ** Heap_List nil bloc_adr 0) s h /\
            eval (var_e fnd) s = eval (nat_e 0) s /\
            eval (var_e stts) s = eval Allocated s /\
            bloc_adr > 0 /\
            eval (var_e sz) s = eval (nat_e 0) s) \/
           (exists bloc_size, exists bloc_status,
            In (bloc_adr, bloc_size, bloc_status) l /\ 
            eval (var_e fnd) s = eval (nat_e 0) s /\
            (eval (var_e stts) s = eval bloc_status s) /\
            bloc_adr > 0 /\
            eval (var_e sz) s = eval (nat_e bloc_size) s
           )
         )         
       )      
       
).

unfold ENTRYSIZE.

Step (

fun (s : store.s) (h : heap.h) =>
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       (exists bloc_adr, 
         eval (var_e entry) s = eval (nat_e bloc_adr) s /\
         (
           ((Heap_List l adr bloc_adr ** Heap_List nil bloc_adr 0) s h /\
            eval (var_e fnd) s = eval (nat_e 0) s /\
            eval (var_e stts) s = eval Allocated s /\
            bloc_adr > 0 /\
            eval (var_e sz) s = eval (nat_e 0) s) \/
           (exists bloc_size, exists bloc_status, 
            In (bloc_adr, bloc_size, bloc_status) l /\ 
            eval (var_e fnd) s = eval (nat_e 0) s /\
            (eval (var_e stts) s = eval bloc_status s) /\
            bloc_adr > 0 /\
            eval (var_e sz) s = eval (nat_e (bloc_adr + 2 + bloc_size)) s
           )
         )         
       )      
       
).

decompose [and] H3; clear H3.
inversion_clear H9 as [bloc_adr].
inversion_clear H3.
inversion_clear H9.

decompose [and] H3; clear H3.
eapply Heap_List_next_last with bloc_adr.
auto.
Decompose_sepcon H9 h1 h2.
Compose_sepcon h2 h1.
auto.
red; auto.
unfold next.
Simpl_eval.
rewrite H8.
Omega_exprb.
red.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists bloc_adr.
split.
Store_update.
left.
split.
Decompose_sepcon H9 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Heap_List_equiv.
split.
Store_update.
split.
Store_update.
split; auto.
Store_update.
inversion_clear H3 as [bloc_size].
inversion_clear H9 as [bloc_status].
decompose [and] H3; clear H3.
generalize (list_split _ _ _ H9); intros.
inversion_clear H3 as [l1].
inversion_clear H12 as [l2].
rewrite H3 in H4.
eapply Heap_List_next.
Compose_sepcon h heap.emp; [idtac | red; auto].
apply H4.
unfold next; simpl; simpl in H8; rewrite H8; Omega_exprb.
red.

split.
rewrite H3.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists bloc_adr.
split.
Store_update.
right.
exists bloc_size.
exists bloc_status.
split.
rewrite H3; intuition.
split.
Store_update.
split.
Store_update.

rewrite H3 in H9.
generalize (Heap_List_block_status _ _ _ _ _ _ _  H4 H9); intros.
inversion_clear H12.
subst bloc_status.
simpl; simpl in H10; auto.
subst bloc_status.
simpl; simpl in H10; auto.
split; auto.
Store_update.

Step (

fun (s : store.s) (h : heap.h) =>
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       (exists bloc_adr, 
         eval (var_e entry) s =  eval (nat_e bloc_adr) s /\
         (
           ((Heap_List l adr bloc_adr ** Heap_List nil bloc_adr 0) s h /\
            eval (var_e fnd) s = eval (nat_e 0) s /\
            eval (var_e stts) s = eval Allocated s /\
            bloc_adr > 0 /\
            eval (var_e sz) s = eval ((nat_e 0) -e (nat_e bloc_adr) -e (nat_e 2)) s) \/
           (exists bloc_size, exists bloc_status, 
            In (bloc_adr, bloc_size, bloc_status) l /\ 
            eval (var_e fnd) s = eval (nat_e 0) s /\
            (eval (var_e stts) s = eval bloc_status s) /\
            bloc_adr > 0 /\
            eval (var_e sz) s = eval (nat_e bloc_size) s
           )
         )         
       )      
       
).

decompose [and] H3; clear H3.
inversion_clear H9 as [bloc_adr].
inversion_clear H3.
red.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists bloc_adr.
split.
Store_update.

inversion_clear H9.
left.
decompose [and] H3; clear H3.
split.
Decompose_sepcon H9 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Heap_List_equiv.
split.
Store_update.
split.
Store_update.
split; auto.
Simpl_eval.
Store_update.

right.
inversion_clear H3 as [bloc_size].
inversion_clear H9 as [bloc_status].
decompose [and] H3; clear H3.
exists bloc_size.
exists bloc_status.
split; auto.
split.
Store_update.
split.
Store_update.
generalize (Heap_List_block_status _ _ _ _ _ _ _  H4 H9); intros.
inversion_clear H3.
subst bloc_status.
Simpl_eval; Omega_exprb.
subst bloc_status.
Simpl_eval; Omega_exprb.
split; auto.
Store_update.

Step TT.

Step TT.

red; intros.
inversion_clear H3.
decompose [and] H4; clear H4.
inversion_clear H10 as [bloc_adr].
inversion_clear H4.
red.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists bloc_adr.
split.
Store_update.

inversion_clear H10.
decompose [and] H4; clear H4.
left.
split.
Decompose_sepcon H10 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Heap_List_equiv.
split.
Store_update.
split.
Store_update.
split; auto.
Store_update.
inversion_clear H4 as [bloc_size].
inversion_clear H10 as [bloc_status].
decompose [and] H4; clear H4.
assert (bloc_size >= 0).
Omega_exprb.
assert (bloc_size < 0).
clear H11; Simpl_eval.
Omega_exprb.
assert (~ (bloc_size >= 0 /\ bloc_size < 0)).
intuition.
intuition.

Step TT.

red.
intros.
inversion_clear H3.
decompose [and] H4; clear H4.
inversion_clear H10 as [bloc_adr].
inversion_clear H4.
split.
Heap_List_equiv.
split; auto.
split.
auto.
split.
auto.
exists bloc_adr.
split.
auto.
inversion_clear H10.

decompose [and] H4; clear H4.
assert (eval (var_e sz) s < 0)%Z.
rewrite H15.
simpl.
Omega_exprb.
assert (eval (var_e sz) s >= 0)%Z.
Eval_b_hyp_clean.
simpl.
Omega_exprb.
assert (~ (eval (var_e sz) s >= 0 /\ eval (var_e sz) s < 0))%Z.
intuition.
intuition.

right.
intuition.

Step TT.

Step TT.
red; intros.
inversion_clear H3.
decompose [and] H4; clear H4.
inversion_clear H10 as [bloc_adr].
inversion_clear H4.
inversion_clear H10.

decompose [and] H4; clear H4.
assert (eval (var_e stts) s = eval Free s).
Omega_exprb.
rewrite H11 in H4.
inversion H4.

inversion_clear H4 as [bloc_size].
inversion_clear H10 as [bloc_status].
decompose [and] H4; clear H4.

red.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists bloc_adr.
split.
Store_update.
right; right; right.
exists bloc_size.
generalize (Heap_List_block_status _ _ _ _ _ _ _ H3 H10); intro X; inversion_clear X.
subst bloc_status.
assert (eval Free s = eval Allocated s).
Simpl_eval.
Omega_exprb.
inversion H4.
subst bloc_status.
split.
Simpl_eval.
Omega_exprb.
split; auto.
Store_update.

Step TT.
red; intros.
inversion_clear H3.
decompose [and] H4; clear H4.
inversion_clear H10 as [bloc_adr].
inversion_clear H4.
inversion_clear H10.

decompose [and] H4; clear H4.
eapply Heap_List_next_last with bloc_adr.
auto.
Decompose_sepcon H10 h1 h2.
Compose_sepcon h2 h1.
auto.
red; auto.
unfold next.
Simpl_eval.
rewrite H9.
Omega_exprb.
red.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists 0.
split.
Store_update.
left.
split; auto.
Store_update.
inversion_clear H4 as [bloc_size].
inversion_clear H10 as [bloc_status].
decompose [and] H4; clear H4.
generalize (list_split _ _ _ H10); intro.
inversion_clear H4 as [l1].
inversion_clear H14 as [l2].
rewrite H4 in H3.
eapply Heap_List_next.
Compose_sepcon h heap.emp.
apply H3.
red; auto.
unfold next.
simpl; simpl in H9.
rewrite H9.
Omega_exprb.
red.
rewrite H4.
split.
Heap_List_equiv.
split; rewrite H4 in H7; auto.
split.
Store_update.
split.
Store_update.
exists (bloc_adr + 2 + bloc_size).
split.
Store_update.

induction l2.
simpl in H3.
right.
left.
simpl.
split.
generalize (Heap_List_last_bloc _ _ _ _ _ _ _ H3); intros.
Decompose_sepcon H14 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Heap_List_equiv.
split.
Store_update.
omega.
clear IHl2.
right.
right.
left.
induction a as [X next_status].
induction X as [next_adr next_size].
exists next_size.
exists next_status.
split.
omega.
split.

generalize (Heap_List_next_bloc _ _ _ _ _ _ _ _ _ _ _ H3); intros.
subst next_adr.
apply in_or_app.
right.
intuition.
Store_update.

red; intros.
inversion_clear H3.
assert (eval (var_e entry) s = eval null s \/ eval (var_e fnd) s = eval (nat_e 1) s).
Simpl_eval.
Omega_exprb.
clear H5.
decompose [and] H4; clear H4.
inversion_clear H10 as [bloc_adr].
inversion_clear H4.
split; auto.
split; auto.
split; auto.
split; auto.
inversion_clear H3.
right; auto.
inversion_clear H10.
inversion_clear H3.
rewrite H4 in H11.
simpl in H11; inversion H11.
inversion_clear H3.
inversion_clear H10.
inversion_clear H11.
rewrite H4 in H10.
simpl in H10; inversion H10.
inversion_clear H10.
inversion_clear H3 as [bloc_size].
inversion_clear H10 as [bloc_status].
decompose [and] H3; clear H3.
rewrite H4 in H13; simpl in H13; inversion H13.
inversion_clear H3 as [bloc_size].
decompose [and] H10; clear H10.
left.
exists bloc_adr.
exists bloc_size.
split; auto.
Qed.
