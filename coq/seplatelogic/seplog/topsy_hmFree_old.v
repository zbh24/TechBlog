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

Open Local Scope Z_scope.

(* Deallocation *)

Definition hmFree (address: loc) (entry: var.v) (addressEntry: var.v) (tmp: var.v) (result: var.v) :=
entry <- (var_e hmStart);
addressEntry <- ((nat_e address) -e (int_e 2%Z));

while ((var_e entry =/= null) &&& (var_e entry =/= var_e addressEntry)) (
   tmp <-* (entry -.> next);
   entry <- (var_e tmp)
);

ifte (var_e entry =/= null) thendo (
   tmp <-* (entry -.> next);
   ifte (var_e tmp =/= null) thendo (
                    (entry -.> status) *<- Free;
                    result <- HM_FREEOK
   ) elsedo ( result <- HM_FREEFAILED)
) elsedo (
   result <- HM_FREEFAILED
).


Close Local Scope Z_scope.

(* hmFree *)

Definition hmFree_specif1 := forall adr sizex x y sizey statusy entry cptr nptr result,  
  (var.set (hmStart::entry::cptr::nptr::result::nil)) -> 
  adr > 0 -> sizex > 0 ->

  {{fun s => fun h => exists l,  (Heap_List l adr 0 ** Array (x+2) sizex) s h /\ 
      In (x,sizex, Allocated) l /\ 
      In (y,sizey, statusy) l /\ 
      x <> y /\
      eval (var_e hmStart) s = eval (nat_e adr) s }}
  
  hmFree (x+2) entry cptr nptr result
  
  {{ fun s => fun h => exists l,  Heap_List l adr 0 s h /\ In (x,sizex,Free) l /\ In (y,sizey,statusy) l /\
        eval (var_e result) s = eval HM_FREEOK s}}.

Definition hmFree_specif2 := forall adr y entry cptr nptr result l,  
  (forall x sizex statusx, In (x,sizex,statusx) l -> x<>y) ->
  (var.set (hmStart::entry::cptr::nptr::result::nil)) -> 
  adr > 0 -> 

  {{fun s => fun h => Heap_List l adr 0 s h /\ 
      eval (var_e hmStart) s = eval (nat_e adr) s }}
  
  hmFree (y+2) entry cptr nptr result
  
  {{ fun s => fun h => Heap_List l adr 0 s h /\
        eval (var_e result) s = eval HM_FREEFAILED s}}.


Lemma hmFree_verif1 : hmFree_specif1.

unfold hmFree_specif1.
unfold hmFree.
intros.
simpl.


Step (fun s => fun h => exists l,
  (Heap_List l adr 0 ** Array (x+2) sizex) s h /\ 
      In (x,sizex, Allocated) l /\ 
      In (y,sizey, statusy) l /\ 
      x <> y /\
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e entry) s = eval (nat_e adr) s).

red; simpl; intros.
inversion_clear H2 as [l].
decompose [and] H3; clear H3.
exists l.
split.
Decompose_sepcon H2 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Array_equiv.
split; auto.
split; auto.
split; auto.
split.
Store_update.
Store_update.

Step (fun s => fun h => exists l,
  (Heap_List l adr 0 ** Array (x+2) sizex) s h /\ 
      In (x,sizex, Allocated) l /\ 
      In (y,sizey, statusy) l /\ 
      x <> y /\
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e entry) s = eval (nat_e adr) s /\
      eval (var_e cptr) s = eval (nat_e x) s).

red; simpl; intros.
inversion_clear H2 as [l].
decompose [and] H3; clear H3.
exists l.
split.
Decompose_sepcon H2 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Array_equiv.
split; auto.
split; auto.
split; auto.
split.
Store_update.
split.
Store_update.
Store_update.


Step (fun s => fun h => exists l,
  (Heap_List l adr 0 ** Array (x+2) sizex) s h /\ 
      In (x,sizex, Allocated) l /\ 
      In (y,sizey, statusy) l /\ 
      x <> y /\
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e cptr) s = eval (nat_e x) s /\
      (exists bloc_adr,  eval (var_e entry) s = eval (nat_e (bloc_adr))  s /\
          bloc_adr > 0 /\ 
             exists l1, exists l2, exists size, exists status,  
               ~(In (x, sizex, Allocated) l1) /\ l = l1 ++ ((bloc_adr, size, status)::nil) ++ l2

     )
).

inversion_clear H2 as [l].
decompose [and] H3; clear H3.
exists l.
split.
auto.
split.
auto.
split.
auto.
split.
auto.
split.
auto.
split.
auto.
exists adr.
split.
Omega_exprb.
split; auto.
exists hl_nil.
induction l.
simpl in H5; contradiction.
clear IHl.
induction a as [X bstatus].
induction X as [badr bsize].
exists l.
exists bsize.
exists bstatus.
split.
red; simpl; intros; contradiction.
Decompose_sepcon H2 h1 h2.
rewrite (Heap_List_equal_start _ _ _ _ _ _ _ _ H3).
auto.


Step (fun s => fun h => exists l,
  (Heap_List l adr 0 ** Array (x+2) sizex) s h /\ 
      In (x,sizex, Allocated) l /\ 
      In (y,sizey, statusy) l /\ 
      x <> y /\
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e cptr) s = eval (nat_e x) s /\
      eval_b ((var_e entry =/= null) &&& (var_e entry =/= var_e cptr)) s = true /\
      (exists bloc_adr,  eval (var_e entry) s = eval (nat_e (bloc_adr))  s /\
          bloc_adr > 0 /\ 
             exists l1, exists l2, exists size, exists status,  
               ~(In (x, sizex, Allocated) l1) /\ l = l1 ++ ((bloc_adr, size, status)::nil) ++ l2 /\
               eval (var_e nptr) s = eval (nat_e (bloc_adr + 2 + size)) s              

     )
).
inversion_clear H2.
inversion_clear H3 as [l].
decompose [and] H2; clear H2.
inversion_clear H11 as [bloc_adr].
decompose [and] H2; clear H2.
inversion_clear H13 as [l1].
inversion_clear H2 as [l2].
inversion_clear H11 as [bloc_size].
inversion_clear H2 as [bloc_status].
inversion_clear H11.
subst l.
Decompose_sepcon H3 h1 h2.
eapply Heap_List_next.
Compose_sepcon h1 h2.
apply H11.
red; auto.
unfold next.
Omega_exprb.
red.

exists (l1 ++ ((bloc_adr, bloc_size, bloc_status) :: nil) ++ l2).
split.
Compose_sepcon h1 h2.
Heap_List_equiv.
Array_equiv.
split; auto.
split; auto.
split; auto.
split.
Store_update.
split.
Store_update.
split.

rewrite <- expr_b_inde_var.
Omega_exprb.
Resolve_not_in_var_list.

exists bloc_adr.
split.
Store_update.
split; auto.
exists l1.
exists l2.
exists bloc_size.
exists bloc_status.
split; auto.
split; auto.
Store_update.


Step TT.
red; intros.
inversion_clear H2 as [l].
decompose [and] H3; clear H3.
inversion_clear H11 as [bloc_adr].
decompose [and] H3; clear H3.
inversion_clear H13 as [l1].
inversion_clear H3 as [l2].
inversion_clear H11 as [bloc_size].
inversion_clear H3 as [bloc_status].
decompose [and] H11; clear H11.
Decompose_sepcon H2 h1 h2.
red.

exists l.
split.
Compose_sepcon h1 h2.
Heap_List_equiv.
Array_equiv.
split.
simpl.
auto.
split.
auto.
split; auto.
split.
Store_update.
split.
Store_update.

exists (bloc_adr + 2 + bloc_size).
split.
Store_update.
split.
omega.

induction l2.
rewrite H14 in H5.
generalize (in_app_or _ _ _ H5); intro X; inversion_clear X.
tauto.
simpl in H16.
simpl in H16; inversion_clear H16; [idtac | contradiction].
injection H18; intros.
assert (bloc_adr <> x).
Simpl_eval.
Omega_exprb.
contradiction.

clear IHl2.
induction a as [X next_status].
induction X as [next_adr next_size].
exists (l1 ++ ((bloc_adr, bloc_size, bloc_status) :: nil)).
exists l2.
exists next_size; exists next_status.
split.
red; intros.
generalize (in_app_or _ _ _ H16); intro X; inversion_clear X.
tauto.
simpl in H18.
simpl in H18; inversion_clear H18; [idtac | contradiction].
injection H19; intros.
assert (bloc_adr <> x).
Simpl_eval.
Omega_exprb.
contradiction.
simpl.

assert (bloc_adr + 2 + bloc_size = next_adr).
rewrite H14 in H11.
simpl in H11.
THeap_List_app_hyp H11; clear H11.
Decompose_sepcon H16 h11 h12.
inversion_clear H20.
subst next x0.
eapply Heap_List_equal_start.
apply H27.
subst next x0.
eapply Heap_List_equal_start.
apply H27.
rewrite H16.
rewrite <- ass_app.
auto.

eapply semax_strengthen_pre with ( fun (s : store.s) (h : heap.h) =>
     (exists l : list (loc * nat * expr),
        (Heap_List l adr 0 ** Array (x + 2) sizex) s h /\
        In (x, sizex, Allocated) l /\
        In (y, sizey, statusy) l /\
        x <> y /\
        eval (var_e hmStart) s = eval (nat_e adr) s /\
        eval (var_e cptr) s = eval (nat_e x) s /\
        eval (var_e entry) s = eval (nat_e x) s /\
        x > 0)
        ).

red; intros.
inversion_clear H2.
inversion_clear H3 as [l].
decompose [and] H2; clear H2.
inversion_clear H11 as [bloc_adr].
decompose [and] H2; clear H2.
inversion_clear H13 as [l1].
inversion_clear H2 as [l2].
inversion_clear H11 as [bloc_size].
inversion_clear H2 as [bloc_status].
inversion_clear H11.
exists l.
split; auto.
split; auto.
split; auto.
split; auto.
split; auto.
split; auto.
split.
Simpl_eval.
Omega_exprb.
Decompose_sepcon H3 h1 h2.
eapply Heap_List_block_adr_pos.
apply H11.
apply H6.

Step TT.

Step (fun (s : store.s) (h : heap.h) =>
        exists l : list (loc * nat * expr),
        (Heap_List l adr 0 ** Array (x + 2) sizex) s h /\
        In (x, sizex, Allocated) l /\
        In (y, sizey, statusy) l /\
        x <> y /\
        eval (var_e hmStart) s = eval (nat_e adr) s /\
        eval (var_e cptr) s = eval (nat_e x) s /\
        eval (var_e entry) s = eval (nat_e x) s /\ 
        x > 0 /\
        eval (var_e nptr) s = eval (nat_e (x + 2 + sizex)) s
        ).

inversion_clear H2.
inversion_clear H3 as [l].
decompose [and] H2; clear H2.
generalize (list_split _ l (x, sizex, Allocated) H6); intro.
inversion_clear H2 as [l1].
inversion_clear H11 as [l2].
Decompose_sepcon H3 h1 h2.
eapply Heap_List_next.
Compose_sepcon h1 h2; [idtac | red; auto].
rewrite H2 in H11; apply H11.
unfold next.
Simpl_eval.
rewrite H10.
Omega_exprb.
red.
exists l.
split.
Compose_sepcon h1 h2.
Heap_List_equiv.
Array_equiv.
split; auto.
split; auto.
split; auto.
split.
Store_update.
split.
Store_update.
split.
Store_update.
split; auto.
Store_update.

Step TT.

Step (fun (s : store.s) (h : heap.h) =>
     (exists l : list (loc * nat * expr),
        (Heap_List l adr 0) s h /\
        In (x, sizex, Free) l /\
        In (y, sizey, statusy) l /\
        x <> y /\
        eval (var_e hmStart) s = eval (nat_e adr) s /\
        eval (var_e cptr) s = eval (nat_e x) s /\
        eval (var_e entry) s = eval (nat_e x) s /\
        x > 0 /\ 
        eval (var_e nptr) s = eval (nat_e (x + 2 + sizex)) s)
).

inversion_clear H2.
inversion_clear H3 as [l].
decompose [and] H2; clear H2.
generalize (list_split _ l (x, sizex, Allocated) H6); intro.
inversion_clear H2 as [l1].
inversion_clear H12 as [l2].
rewrite H2 in H3.
generalize (change_status_Alloc_to_Free l1 l2 _ _ _ _ _ H0 H3); intros.
inversion_clear H12 as [e].
Decompose_sepcon H14 h1 h2.
exists e.
Compose_sepcon h1 h2.
Simpl_eval.
unfold status.
Mapsto.
Intro_sepimp h'1 h'.
assert (h2 # h'1 /\ (nat_e x |-> Free) s h'1).
split; [Disjoint_heap | Simpl_eval; unfold status in H18; Mapsto].
generalize (H17 h'1 H20 h' H19); intros.
exists (l1 ++ ((x, sizex, Free) :: nil) ++ l2).
split.
auto.
split.
auto with *.
split.
rewrite H2 in H5.
generalize (in_app_or _ _ _ H5); intro X; inversion_clear X.
eapply in_or_app.
left; auto.
simpl in H22; inversion_clear H22.
injection H23; intros; contradiction.
eapply in_or_app.
right; simpl; right; auto.
split; auto.

Step TT.

red; intros.
inversion_clear H2.
inversion_clear H3 as [l].
decompose [and] H2; clear H2.
red.
unfold HM_FREEOK.
simpl.
exists x0.
split.
Heap_List_equiv.
split; auto.
split; auto.
Store_update.

Step TT.

red; intros.
inversion_clear H2.
inversion_clear H3 as [l].
decompose [and] H2; clear H2.
assert (eval (var_e nptr) s = 0%Z).
unfold null in H4.
Omega_exprb.
rewrite H13 in H2.
assert (x + 2 + sizex = 0).
Omega_exprb.
assert (x + 2 + sizex <> 0).
Omega_exprb.
tauto.


Step TT.
red; intros.
inversion_clear H2.
inversion_clear H3 as [l].
decompose [and] H2; clear H2.
assert (eval (var_e entry) s = 0%Z).
Simpl_eval.
unfold null in H4.
Omega_exprb.
rewrite H10 in H2.
assert (x = 0).
Simpl_eval.
Omega_exprb.
subst x; inversion H12.
Qed.



Lemma hmFree_verif2 : hmFree_specif2.

unfold hmFree_specif2.
unfold hmFree.
intros.
simpl proj_cmd.

Step (
fun (s : store.s) (h : heap.h) =>
     Heap_List l adr 0 s h /\ 
     eval (var_e hmStart) s = eval (nat_e adr) s /\
     eval (var_e entry) s = eval (nat_e adr) s
).
inversion_clear H2.
red.
Simpl_eval.
split.
Heap_List_equiv.
split.
Store_update.
Store_update.

Step (
fun (s : store.s) (h : heap.h) =>
     Heap_List l adr 0 s h /\ 
     eval (var_e hmStart) s = eval (nat_e adr) s /\
     eval (var_e entry) s = eval (nat_e adr) s /\
     eval (var_e cptr) s = eval (nat_e y) s 
).
inversion_clear H2.
decompose [and] H4; clear H4.
red.
Simpl_eval.
split.
Heap_List_equiv.
split.
Store_update.
split.
Store_update.
Store_update.

Step (
fun (s : store.s) (h : heap.h) =>
     Heap_List l adr 0 s h /\ 
     eval (var_e hmStart) s = eval (nat_e adr) s /\
     eval (var_e cptr) s = eval (nat_e y) s /\
     (exists bloc_adr, eval (var_e entry) s = eval (nat_e bloc_adr) s /\
        (
          (exists bloc_size, exists bloc_status,
           In (bloc_adr, bloc_size, bloc_status) l) \/
           
           (Heap_List l adr bloc_adr ** Heap_List nil bloc_adr 0) s h \/
           
           bloc_adr = 0
           
        )   
     )
).

decompose [and] H2; clear H2.
Simpl_eval.

split; auto.
split; auto.
split; auto.
exists adr.
split; auto.

induction l.

right; left.
Compose_sepcon heap.emp h.
eapply Heap_List_trans; [auto | auto | red; auto].
auto.

clear IHl.

induction a as [X begin_status].
induction X as [begin_adr begin_size].
left.
exists begin_size; exists begin_status.
rewrite (Heap_List_equal_start _ _ _ _ _ _ _ _ H3).
auto with *.

Step (fun (s : store.s) (h : heap.h) =>
     (Heap_List l adr 0 s h /\
      eval (var_e hmStart) s = eval (nat_e adr) s /\
      eval (var_e cptr) s = eval (nat_e y) s /\
      eval_b ((var_e entry =/= null) &&& (var_e entry =/= var_e cptr)) s = true /\
      (exists bloc_adr : nat,
         eval (var_e entry) s = eval (nat_e bloc_adr) s /\
         ((exists bloc_size : nat,
             (exists bloc_status : expr,
                In (bloc_adr, bloc_size, bloc_status) l /\ 
                eval (var_e nptr) s = eval (nat_e (bloc_adr + 2 + bloc_size)) s
                )) \/
          (Heap_List l adr bloc_adr ** Heap_List nil bloc_adr 0) s h /\
          eval (var_e nptr) s = eval (nat_e 0) s
          )))
).
inversion_clear H2.
decompose [and] H3; clear H3.
inversion_clear H8 as [bloc_adr].
inversion_clear H3.
inversion_clear H8.

inversion_clear H3 as [bloc_size].
inversion_clear H8 as [bloc_status].
generalize (list_split _ l (bloc_adr, bloc_size, bloc_status) H3); intros.
inversion_clear H8 as [l1].
inversion_clear H9 as [l2].
rewrite H8 in H2.
eapply Heap_List_next.
Compose_sepcon h heap.emp; [idtac | red; auto].
apply H2.
unfold next.
Simpl_eval.
rewrite H7.
Omega_exprb.
red.
split.
rewrite H8.
Heap_List_equiv.
split.
Store_update.
split.
Store_update.
split.
Store_update.
exists bloc_adr.
split.
Store_update.
left.
exists bloc_size; exists bloc_status.
split; auto.
Store_update.

inversion_clear H3.
eapply semax_lookup_simple with (nat_e 0).

Decompose_sepcon H8 h1 h2.
inversion_clear H11; [idtac | inversion H10].
subst next; clear H10. 
simpl in H14.
Decompose_sepcon H14 h21 h22.
Decompose_sepcon H15 h221 h222.
Compose_sepcon h221 (h1 +++ h21).
unfold next. 
Mapsto. 
red; auto.

red.
split.
Heap_List_equiv.
split.
Store_update.
split.
Store_update.
split.

rewrite <- expr_b_inde_var.
Omega_exprb.
Resolve_not_in_var_list.

exists bloc_adr.
split.
Store_update.
right.
split.
Decompose_sepcon H8 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Heap_List_equiv.
Store_update.
subst bloc_adr.
assert (eval (var_e entry) s <> eval null s).
Omega_exprb.
unfold null in H3.
tauto.


Step TT.

red; intros.
decompose [and] H2; clear H2.
inversion_clear H8 as [bloc_adr].
inversion_clear H2.
red.
split.
Heap_List_equiv.
split.
Store_update.
split.
Store_update.
inversion_clear H8.

inversion_clear H2 as [bloc_size].
inversion_clear H8 as [bloc_status].
inversion_clear H2.
exists (bloc_adr + 2 + bloc_size).
split.
Store_update.
generalize (list_split _ l (bloc_adr, bloc_size, bloc_status) H8); intros.
inversion_clear H2 as [l1].
inversion_clear H10 as [l2].
induction l2.

simpl in H2.
right; left.
rewrite H2 in H3.
generalize (Heap_List_last_bloc _ _ _ _ _ _ _ H3); intros.
rewrite H2.
Decompose_sepcon H10 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Heap_List_equiv.

clear IHl2.
left.
induction a; induction a.
assert (a = bloc_adr + 2 + bloc_size).
rewrite H2 in H3.
simpl in H3.
eapply Heap_List_next_bloc.
simpl.
apply H3.
subst a.
exists b0; exists b.
rewrite H2.
eapply in_or_app.
right.
simpl.
right; left.
auto.
inversion_clear H2.

exists 0.
split.
Store_update.
right; right.
auto.

Step TT.

eapply semax_strengthen_pre with (

fun (s : store.s) (h : heap.h) =>
     Heap_List l adr 0 s h /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e cptr) s = eval (nat_e y) s /\
       (exists bloc_adr : nat,
          eval (var_e entry) s = eval (nat_e bloc_adr) s /\
          (Heap_List l adr bloc_adr ** Heap_List nil bloc_adr 0) s h /\
          eval_b (var_e entry == var_e cptr) s = true /\ 
          eval_b (var_e entry =/= null) s = true)

).


red; intros.
decompose [and] H2; clear H2.
inversion_clear H9 as [bloc_adr].
inversion_clear H2.
inversion_clear H9.
inversion_clear H2 as [bloc_size].
inversion_clear H9 as [bloc_status].
generalize (H _ _ _ H2); intros.
assert (bloc_adr = y).
Simpl_eval.
Omega_exprb.
contradiction.
inversion_clear H2.
split; auto.
split; auto.
split; auto.
exists bloc_adr.
split; auto.
split; auto.
split; auto.
Omega_exprb.
unfold null in H4.
assert (bloc_adr <> 0).
Simpl_eval.
Omega_exprb.
contradiction.

Step (

fun (s : store.s) (h : heap.h) =>
     Heap_List l adr 0 s h /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e cptr) s = eval (nat_e y) s /\
       eval (var_e nptr) s = eval null s /\
       (exists bloc_adr : nat,
          eval (var_e entry) s = eval (nat_e bloc_adr) s /\
          (Heap_List l adr bloc_adr ** Heap_List nil bloc_adr 0) s h /\
          eval_b (var_e entry == var_e cptr) s = true /\ 
          eval_b (var_e entry =/= null) s = true)

).

decompose [and] H2; clear H2.
inversion_clear H7 as [bloc_adr].
decompose [and] H2; clear H2.
eapply Heap_List_next_last with bloc_adr.
Simpl_eval.
Omega_exprb.
Decompose_sepcon H8 h1 h2.
Compose_sepcon h2 h1.
auto.
red; auto.
unfold next.
Simpl_eval.
rewrite H6.
Omega_exprb.
red; intros.
split.
Heap_List_equiv.
split.
Store_update.
split.
Store_update.
split.
Store_update.
exists bloc_adr.
split.
Store_update.
split.
Decompose_sepcon H8 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Heap_List_equiv.
split.
Store_update.
Store_update.

Step TT.

eapply semax_strengthen_pre with (fun s:store.s => fun h:heap.h => False).

red; intros.
decompose [and] H2; clear H2.
unfold null in H7.
unfold null in H4.
assert (eval (var_e nptr) s <> eval (int_e 0%Z) s).
Omega_exprb.
contradiction.

Step (fun s:store.s => fun h:heap.h => False).
contradiction.
Step (fun s:store.s => fun h:heap.h => False).
red; intros.
contradiction.

Step TT.
red; intros.
decompose [and] H2; clear H2.
red; intros.
split.
Heap_List_equiv.
Store_update.

Step TT.
red; intros.
inversion_clear H2.
inversion_clear H3.
decompose [and] H2; clear H2.
red; intros.
split.
Heap_List_equiv.
Store_update.
Qed.  



