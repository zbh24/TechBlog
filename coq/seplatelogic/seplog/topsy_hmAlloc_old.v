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

(* Allocation *)

Definition ENTRYSIZE (x:var.v) (tmp:var.v) := 
  tmp <-* (x -.> next);
  tmp <- (var_e tmp -e var_e x -e int_e 2%Z);
  ifte (nat_e 0 >> var_e tmp) thendo (tmp <- nat_e 0) elsedo skip.

Definition findFree (size: nat) (entry fnd sz stts:var.v) :=

entry <- var_e hmStart;
stts <-* (entry -.> status);
fnd <- int_e 0;

(while ((var_e entry =/= null) &&& (var_e fnd =/= int_e 1)) (
  stts <-* (entry -.> status);
  (ENTRYSIZE entry sz);
  (ifte ((var_e stts == Free) &&& (var_e sz >>= nat_e size)) thendo 
    (fnd <- int_e 1)
    elsedo 
    (entry <-* (entry -.> next)))
)).

Definition LEFTOVER : nat := 8%nat.

Definition compact (cptr nptr stts : var.v) :=

while (var_e cptr =/= null) (

   stts <-* (cptr -.> status);

   ifte (var_e stts ==  Free) thendo (

   nptr <-* (cptr -.> next); 
   stts <-* (nptr -.> status);

   (while (var_e stts == Free) (

           stts <-* (nptr -.> next);
           (cptr -.> next) *<- var_e stts;
           nptr <- var_e stts;
           stts <-* (nptr -.> status)

     )
    )

   ) elsedo skip;
 
   cptr <-* (cptr -.> next)
).

(* entry contains the address of a free entry, size is the size we want to allocated *)
Definition split (entry:var.v) (size:nat) (cptr sz:var.v) :=
ENTRYSIZE entry sz;
ifte (var_e sz >>= (nat_e size +e nat_e LEFTOVER +e nat_e 2%nat)) thendo (
  cptr <- var_e entry +e nat_e 2%nat +e nat_e size;
  sz <-* (entry -.> next);
  (cptr -.> next) *<- var_e sz;
  (cptr -.> status) *<- Free;
  (entry -.> next) *<- var_e cptr
) elsedo (
  skip
);
(entry -.> status) *<- Allocated.

Definition HM_ALLOCFAILED := int_e 0%Z.
Definition HM_ALLOCOK := int_e 1%Z.

Definition hmAlloc (result:var.v) (size: nat) (entry:var.v) (*(adr: loc)*) (cptr fnd stts nptr sz:var.v) :=
(* entry <- (nat_e adr); cette instruction ne sert a rien*)
result <- null;
findFree size entry fnd sz stts;
(ifte (var_e entry == null) thendo (
(*  tmp <- (var_e adr);*)
  cptr <- var_e hmStart;
  compact cptr nptr stts;
  findFree size entry fnd sz stts
) elsedo (
  skip
));
(ifte (var_e entry == null) thendo (
  result <- HM_ALLOCFAILED
) elsedo (
  split entry size cptr sz;
  result <- var_e entry +e nat_e 2%nat
)).

Close Local Scope Z_scope.

(* hmAlloc Specification *)

Definition hmAlloc_specif1 := forall result adr sizex x size entry cptr fnd stts nptr sz, 
  (var.set (hmStart::result::entry::cptr::fnd::stts::nptr::sz::nil)) -> 
  adr > 0 -> sizex > 0 -> size > 0 ->

  {{fun s h => exists l,  
        Heap_List l adr 0 s h /\
        In (x,sizex,Allocated) l /\
        eval (var_e hmStart) s = eval (nat_e adr) s }}
  
  hmAlloc result size entry cptr fnd stts nptr sz
  
  {{ fun s h => 
    (exists l, exists y, y > 0 /\ eval (var_e result) s = Z_of_nat (y+2) /\
      (exists size'', size'' >= size /\
      (Heap_List l adr 0 ** Array (y + 2) size'') s h /\ 
      In (x,sizex,Allocated) l /\ 
      In (y,size'',Allocated) l /\ 
      x <> y))

    \/

    (exists l, eval (var_e result) s = 0%Z /\ Heap_List l adr 0 s h /\ In (x,sizex,Allocated) l) }}.

Definition findFree_specif1 := forall adr entry fnd sz stts size sizex x result,
    size > 0 ->
    sizex > 0 ->
    adr > 0 ->
    var.set (hmStart::entry::fnd::sz::stts::result::nil) ->

    {{fun s h =>exists l,  Heap_List l adr 0 s h /\ 
    In (x,sizex,Allocated) l /\
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s }}

    findFree size entry fnd sz stts

    {{fun s h =>  exists l,
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

Definition compact_specif1:= forall adr cptr nptr stts size sizex x result entry,
    size > 0 ->
    sizex > 0 ->
    adr > 0 ->
    var.set (hmStart::entry::cptr::nptr::stts::result::nil) ->

    {{fun s h =>exists l, Heap_List l adr 0 s h /\ 
        In (x,sizex,Allocated) l /\
        eval (var_e hmStart) s = eval (nat_e adr) s /\
        eval (var_e result) s = eval null s /\    
        eval (var_e cptr) s = eval (nat_e adr) s
    }}
        
        compact cptr nptr stts
        
    {{fun s h => exists l, Heap_List l adr 0 s h /\ 
        In (x,sizex,Allocated) l /\
        eval (var_e hmStart) s = eval (nat_e adr) s /\
        eval (var_e result) s = eval null s 
    }}.

Definition split_specif1 := forall adr cptr sz size sizex x result entry, 
    size > 0 ->
    sizex > 0 ->
    adr > 0 ->
    var.set (hmStart::entry::cptr::sz::result::nil) ->

{{fun s h =>  exists l,
    Heap_List l adr 0 s h /\ 
    In (x,sizex,Allocated) l /\ 
    eval (var_e hmStart) s = eval (nat_e adr) s /\
    eval (var_e result) s = eval null s /\    
    (exists finded_free_block, exists size'', size'' >= size /\ 
     In (finded_free_block,size'',Free) l /\ 
     eval (var_e entry) s = (Z_of_nat finded_free_block) /\ 
     finded_free_block > 0 /\
     finded_free_block <> x) }}

   split entry size cptr sz

{{fun s h => exists l,
    In (x,sizex,Allocated) l /\ 
    (exists y, y > 0 /\ eval (var_e entry) s = Z_of_nat (y) /\
      (exists size'', size'' >= size /\      
       (Heap_List l adr 0 ** Array (y+2) size'') s h /\ 
       In (y,size'',Allocated) l /\ y <> x))}}.

Lemma findFree_verif1 : findFree_specif1.
unfold findFree_specif1.
intros.
unfold findFree.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       eval (var_e entry) s = eval (nat_e adr) s

).

inversion_clear H3 as [l].
red.
exists l.
decompose [and] H4; clear H4.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
Store_update.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       eval (var_e entry) s = eval (nat_e adr) s /\
       (eval (var_e stts) s = eval Allocated s \/ eval (var_e stts) s = eval Free s)
       
).

inversion_clear H3 as [l].
decompose [and] H4; clear H4.
induction l.
simpl in H6; contradiction.
clear IHl.
induction a as [X bloc_status].
induction X as [bloc_adr bloc_size].
assert (In (bloc_adr, bloc_size, bloc_status) ((bloc_adr, bloc_size, bloc_status) :: l)).
auto with *.
eapply Heap_List_status.
apply H4.
Compose_sepcon h heap.emp.
apply H3.
red; auto.
generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H3); intros.
unfold status.
Simpl_eval.
Omega_exprb.

red.
exists ((bloc_adr, bloc_size, bloc_status) :: l).
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
split.
Store_update.
generalize (Heap_List_block_status _ _ _ _ _ _ _ H3 H4); intros.
inversion_clear H8.
subst bloc_status.
Store_update.
subst bloc_status.
Store_update.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       eval (var_e entry) s = eval (nat_e adr) s /\
       (eval (var_e stts) s = eval Allocated s \/ eval (var_e stts) s = eval Free s) /\
       eval (var_e fnd) s = eval (nat_e 0) s
       
).

red.
inversion_clear H3 as [l].
decompose [and] H4; clear H4.
exists l.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
Store_update.

Step (

fun s h => exists l,
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
inversion_clear H3 as [l].
decompose [and] H4; clear H4.
exists l.
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
generalize (Heap_List_equal_start _ _ _ _ _ _ _ _ H3); intros.
subst adr.
exists bloc_size.
exists bloc_status.
split; auto.
split.
auto with *.
auto.

Step (

fun s h => exists l,
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
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10 as [bloc_adr].
inversion_clear H3.

inversion_clear H10.

inversion_clear H3.
assert (bloc_adr <> 0).
Simpl_eval.
Omega_exprb.
contradiction.

inversion_clear H3.
decompose [and] H10; clear H10.
eapply Heap_List_status_last.
apply H13.
Decompose_sepcon H3 h1 h2.
Compose_sepcon h2 h1.
auto.
red; auto.
unfold status.
Simpl_eval.
Omega_exprb.
red.
exists l.
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
Decompose_sepcon H3 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Heap_List_equiv.
split.
Store_update.
Store_update.

inversion_clear H10.
inversion_clear H3 as [bloc_size].
inversion_clear H10 as [bloc_status].
decompose [and] H3; clear H3.

eapply Heap_List_status.
apply H12.
Compose_sepcon h heap.emp.
apply H4.
red; auto.
unfold status.
Simpl_eval.
Omega_exprb.
red.
exists l.
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
generalize (Heap_List_block_status _ _ _ _ _ _ _ H4 H12); intro X; inversion_clear X.
subst bloc_status.
Store_update.
subst bloc_status.
Store_update.

inversion_clear H3 as [bloc_size].
decompose [and] H10; clear H10.
assert (eval (var_e fnd) s <> eval (nat_e 1) s).
Omega_exprb.
contradiction.

Step (

fun s h => exists l,
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

fun s h => exists l,
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

inversion_clear H3 as [l].
decompose [and] H4; clear H4.
inversion_clear H9 as [bloc_adr].
inversion_clear H4.
inversion_clear H9.

decompose [and] H4; clear H4.
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
exists l.
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
inversion_clear H4 as [bloc_size].
inversion_clear H9 as [bloc_status].
decompose [and] H4; clear H4.
generalize (list_split _ _ _ H9); intros.
inversion_clear H4 as [l1].
inversion_clear H12 as [l2].
rewrite H4 in H3.
eapply Heap_List_next.
Compose_sepcon h heap.emp; [idtac | red; auto].
apply H3.
unfold next; simpl; simpl in H8; rewrite H8; Omega_exprb.
red.
exists l.

split.
rewrite H4.
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
rewrite H4; intuition.
split.
Store_update.
split.
Store_update.

rewrite H4 in H9.
generalize (Heap_List_block_status _ _ _ _ _ _ _  H3 H9); intros.
inversion_clear H12.
subst bloc_status.
simpl; simpl in H10; auto.
subst bloc_status.
simpl; simpl in H10; auto.
split; auto.
Store_update.

Step (

fun s h => exists l,
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
inversion_clear H3 as [l].
decompose [and] H4; clear H4.
inversion_clear H9 as [bloc_adr].
inversion_clear H4.
red.
exists l.
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
decompose [and] H4; clear H4.
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
inversion_clear H4 as [bloc_size].
inversion_clear H9 as [bloc_status].
decompose [and] H4; clear H4.
exists bloc_size.
exists bloc_status.
split; auto.
split.
Store_update.
split.
Store_update.
generalize (Heap_List_block_status _ _ _ _ _ _ _  H3 H9); intros.
inversion_clear H4.
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
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10 as [bloc_adr].
inversion_clear H3.
red.
exists l.
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
decompose [and] H3; clear H3.
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
inversion_clear H3 as [bloc_size].
inversion_clear H10 as [bloc_status].
decompose [and] H3; clear H3.
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
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10 as [bloc_adr].
inversion_clear H3.
exists l.
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

decompose [and] H3; clear H3.
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
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10 as [bloc_adr].
inversion_clear H3.
inversion_clear H10.

decompose [and] H3; clear H3.
assert (eval (var_e stts) s = eval Free s).
Omega_exprb.
rewrite H11 in H3.
inversion H3.

inversion_clear H3 as [bloc_size].
inversion_clear H10 as [bloc_status].
decompose [and] H3; clear H3.

red.
exists l.
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
generalize (Heap_List_block_status _ _ _ _ _ _ _ H4 H10); intro X; inversion_clear X.
subst bloc_status.
assert (eval Free s = eval Allocated s).
Simpl_eval.
Omega_exprb.
inversion H3.
subst bloc_status.
split.
Simpl_eval.
Omega_exprb.
split; auto.
Store_update.

Step TT.
red; intros.
inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10 as [bloc_adr].
inversion_clear H3.
inversion_clear H10.

decompose [and] H3; clear H3.
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
exists l.
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
inversion_clear H3 as [bloc_size].
inversion_clear H10 as [bloc_status].
decompose [and] H3; clear H3.
generalize (list_split _ _ _ H10); intro.
inversion_clear H3 as [l1].
inversion_clear H14 as [l2].
rewrite H3 in H4.
eapply Heap_List_next.
Compose_sepcon h heap.emp.
apply H4.
red; auto.
unfold next.
simpl; simpl in H9.
rewrite H9.
Omega_exprb.
red.
exists l.
rewrite H3.
split.
Heap_List_equiv.
split; rewrite H3 in H7; auto.
split.
Store_update.
split.
Store_update.
exists (bloc_adr + 2 + bloc_size).
split.
Store_update.

induction l2.
simpl in H4.
right.
left.
simpl.
split.
generalize (Heap_List_last_bloc _ _ _ _ _ _ _ H4); intros.
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

generalize (Heap_List_next_bloc _ _ _ _ _ _ _ _ _ _ _ H4); intros.
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
inversion_clear H4 as [l].
decompose [and] H5; clear H5.
inversion_clear H10 as [bloc_adr].
inversion_clear H5.
exists l.
split; auto.
split; auto.
split; auto.
split; auto.
inversion_clear H3.
right; auto.
inversion_clear H10.
inversion_clear H3.
rewrite H5 in H11.
simpl in H11; inversion H11.
inversion_clear H3.
inversion_clear H10.
rewrite H5 in H11.
simpl in H11; inversion H11.
inversion_clear H10.
inversion_clear H10.
inversion_clear H3 as [bloc_size].
inversion_clear H10 as [bloc_status].
decompose [and] H3; clear H3.
rewrite H5 in H13; simpl in H13; inversion H13.
inversion_clear H3 as [bloc_size].
decompose [and] H10; clear H10.
left.
exists bloc_adr.
exists bloc_size.
split; auto.
Qed.

Lemma compact_verif1 : compact_specif1.
unfold compact_specif1.
intros.
unfold compact.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
       ( (cur_adr = 0) \/
         ((Heap_List l adr cur_adr ** Heap_List nil cur_adr 0) s h /\
            cur_adr > 0) \/
         (exists cur_size, exists cur_status, In (cur_adr, cur_size, cur_status) l /\
            cur_adr > 0)
       )
).

red; intros.
inversion_clear H3 as [l].
decompose [and] H4; clear H4.
exists l.
split; auto.
split; auto.
split; auto.
split; auto.
exists adr.
split; auto.
right; right.

induction l.
simpl in H6; contradiction.
clear IHl.
induction a as [X cur_status].
induction X as [cur_adr cur_size].
exists cur_size.
exists cur_status.
rewrite (Heap_List_equal_start _ _ _ _ _ _ _ _ H3).
split.
auto with *.
rewrite <- (Heap_List_equal_start _ _ _ _ _ _ _ _ H3).
auto.


Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
       ( ((Heap_List l adr cur_adr ** Heap_List nil cur_adr 0) s h /\
            eval (var_e stts) s = eval Allocated s /\
            cur_adr > 0) \/
         (exists cur_size, exists cur_status, In (cur_adr, cur_size, cur_status) l /\
            eval (var_e stts) s = eval cur_status s /\
            cur_adr > 0)
       )
).
inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10 as [cur_adr].
inversion_clear H3.
inversion_clear H10.
assert (cur_adr <> 0).
Simpl_eval.
Omega_exprb.
contradiction.
inversion_clear H3.
inversion_clear H10.
eapply Heap_List_status_last.
apply H11.
Decompose_sepcon H3 h1 h2.
Compose_sepcon h2 h1.
auto.
red; auto.
unfold status.
Simpl_eval.
rewrite H9.
Omega_exprb.
red.
exists l.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists cur_adr.
split.
Store_update.
left.
split.
Decompose_sepcon H3 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Heap_List_equiv.
Store_update.
inversion_clear H10 as [cur_size].
inversion_clear H3 as [cur_status].
inversion_clear H10.
eapply Heap_List_status with (startl := adr).
apply H3.
Compose_sepcon h heap.emp.
Heap_List_equiv.
red; auto.
unfold status.
Simpl_eval.
rewrite H9.
Omega_exprb.
red.
exists l.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists cur_adr.
split.
Store_update.
right.
exists cur_size.
exists cur_status.
split; auto.
split.
generalize (Heap_List_block_status _ _ _ _ _ _ _ H4 H3); intro X; inversion_clear X.
subst cur_status.
Store_update.
subst cur_status.
Store_update.
auto.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
       ( ((Heap_List l adr cur_adr ** Heap_List nil cur_adr 0) s h /\
            cur_adr > 0) \/
         (exists cur_size, exists cur_status, In (cur_adr, cur_size, cur_status) l /\
            cur_adr > 0)
       )
).

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
       (exists cur_size, 
            In (cur_adr, cur_size, Free) l /\            
            eval (var_e nptr) s = eval (nat_e (cur_adr + 2 + cur_size)) s /\
            cur_adr > 0
       )
).
inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10 as [cur_adr].
inversion_clear H3.
inversion_clear H10.
decompose [and] H3; clear H3.
assert (eval (var_e stts) s = eval Free s).
Omega_exprb.
rewrite H3 in H12; simpl in H12.
inversion H12.
inversion_clear H3 as [cur_size].
inversion_clear H10 as [cur_status].
decompose [and] H3; clear H3.

eapply Heap_List_next'.
apply H10.
Compose_sepcon h heap.emp.
apply H4.
red; auto.
unfold next.
simpl.
simpl in H9.
rewrite H9.
OmegaZ.
red.
exists l.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists cur_adr.
split.
Store_update.
exists cur_size.
generalize (Heap_List_block_status _ _ _ _ _ _ _ H4 H10); intros.
inversion_clear H3.
subst cur_status.
assert (eval (var_e stts) s = eval Free s).
Omega_exprb.
rewrite H12 in H3; inversion H3.
subst cur_status.
split; auto.
split.
Store_update.
auto.


Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
       (exists cur_size, 
            In (cur_adr, cur_size, Free) l /\            
            eval (var_e nptr) s = eval (nat_e (cur_adr + 2 + cur_size)) s /\
            cur_adr > 0 /\ (
            (exists next_size, 
                exists next_status, 
                   In ((cur_adr + 2 + cur_size), next_size, next_status) l /\
                   eval (var_e stts) s = eval next_status s) \/
                   
                   ((Heap_List l adr  (cur_adr + 2 + cur_size) ** Heap_List nil (cur_adr + 2 + cur_size) 0) s h /\
                     eval (var_e stts) s = eval Allocated s)

            )

       )
).

inversion_clear H3 as [l].
decompose [and] H4; clear H4.
inversion_clear H9 as [cur_adr].
inversion_clear H4.
inversion_clear H9 as [cur_size].
decompose [and] H4; clear H4.

generalize (list_split _ _ _ H9); intro.
inversion_clear H4 as [l1].
inversion_clear H10 as [l2].

induction l2.
simpl in H4.

eapply Heap_List_status_last with (bloc_adr := cur_adr + 2 + cur_size).
omega.
rewrite H4 in H3.
generalize (Heap_List_last_bloc _ _ _ _ _ _ _ H3); intros.
Decompose_sepcon H10 h1 h2.
Compose_sepcon h2 h1.
auto.
red; auto.
unfold status.
Simpl_eval.
rewrite H11.
OmegaZ.

red.
exists l.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists cur_adr.
split.
Store_update.
exists cur_size.
split; auto.
split.
Store_update.
split; auto.
right.
split.
rewrite H4 in H3.
generalize (Heap_List_last_bloc _ _ _ _ _ _ _ H3); intro.
Decompose_sepcon H10 h1 h2.
Compose_sepcon h1 h2.
rewrite H4.
Heap_List_equiv.
Heap_List_equiv.
Store_update.

clear IHl2.

induction a as [X next_status].
induction X as [next_adr next_size].

assert (In (next_adr, next_size, next_status) l).
rewrite H4.
auto with *.

eapply Heap_List_status.

apply H10.
Compose_sepcon h heap.emp.
apply H3.
red; auto.
unfold status.
Simpl_eval.
rewrite H11.
assert (next_adr = cur_adr + 2 + cur_size).
rewrite H4 in H3.
eapply Heap_List_next_bloc.
simpl in H3.
simpl.
apply H3.
OmegaZ.

red.

exists l.
split.

Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists cur_adr.
split.
Store_update.
exists cur_size.
split; auto.
split.
Store_update.
split; auto.
left.
exists next_size.
exists next_status.
assert (next_adr = cur_adr + 2 + cur_size).
rewrite H4 in H3.
eapply Heap_List_next_bloc.
simpl in H3.
simpl.
apply H3.
split.
rewrite H4; rewrite H13; intuition.
assert(In (next_adr, next_size, next_status) l).
rewrite H4; intuition.
generalize (Heap_List_block_status _ _ _ _ _ _ _ H3 H14); intro X; inversion_clear X.
subst next_status.
Store_update.
subst next_status.
Store_update.


Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
       (exists cur_size, 
            In (cur_adr, cur_size, Free) l /\            
            eval (var_e nptr) s = eval (nat_e (cur_adr + 2 + cur_size)) s /\
            cur_adr > 0 /\ (
            (exists next_size, 
                exists next_status, 
                   In ((cur_adr + 2 + cur_size), next_size, next_status) l /\
                   eval (var_e stts) s = eval next_status s) \/
                   
                   ((Heap_List l adr  (cur_adr + 2 + cur_size) ** Heap_List nil (cur_adr + 2 + cur_size) 0) s h /\
                     eval (var_e stts) s = eval Allocated s)
            )
       )
).

red; intros.
trivial.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
       (exists cur_size, 
            In (cur_adr, cur_size, Free) l /\            
            eval (var_e nptr) s = eval (nat_e (cur_adr + 2 + cur_size)) s /\
            cur_adr > 0 /\ (
            (exists next_size, 
                   In ((cur_adr + 2 + cur_size), next_size, Free) l /\
                   eval (var_e stts) s = eval (nat_e (cur_adr + 2 + cur_size + 2 + next_size)) s) 
            )
       )
).

inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10 as [cur_adr].
inversion_clear H3.
inversion_clear H10 as [cur_size].
decompose [and] H3; clear H3.
inversion_clear H14.
inversion_clear H3 as [next_size].
inversion_clear H13 as [next_status].
inversion_clear H3.

assert (next_status = Free).
assert (eval (var_e stts) s = eval Free s).
Omega_exprb.
generalize (Heap_List_block_status _ _ _ _ _ _ _ H4 H13); intro X; inversion_clear X.
subst next_status.
rewrite H3 in H14; inversion H14.
auto.
subst next_status.
generalize (list_split _ _ _ H13); intros.
inversion_clear H3 as [l1].
inversion_clear H15 as [l2].
rewrite H3 in H4.
eapply Heap_List_next.
Compose_sepcon h heap.emp; [apply H4 | red; auto].
Simpl_eval.
unfold next.
rewrite H12.
OmegaZ.
red.
exists l.
split.
rewrite H3.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists cur_adr.
split.
Store_update.
exists cur_size.
split; auto.
split.
Store_update.
split; auto.
exists next_size.
split; auto.
Store_update.

inversion_clear H3.
assert (eval (var_e stts) s = eval Free s).
Omega_exprb.
rewrite H3 in H14; inversion H14.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
       (exists cur_size, 
            In (cur_adr, cur_size, Free) l /\            
            cur_adr > 0 /\
            eval (var_e stts) s = eval (nat_e (cur_adr + 2 + cur_size)) s
       )
).
inversion_clear H3 as [l].
decompose [and] H4; clear H4.
inversion_clear H9 as [cur_adr].
inversion_clear H4.
inversion_clear H9 as [cur_size].
decompose [and] H4; clear H4.
inversion_clear H13 as [next_size].
decompose [and] H4; clear H4.

generalize (Heap_List_list_split_cont _ _ _ _ _ _ _ _ _ H3 H9 H12); intros.
inversion_clear H4 as [l1].
inversion_clear H14 as [l2].
rewrite H4 in H3.
generalize (Compaction _ _ _ _ _ _ _ _ H1 H3); intros.
Decompose_sepcon H14 h1 h2.
exists (nat_e (cur_adr + 2 + cur_size)).
Compose_sepcon h1 h2.
unfold next.
Simpl_eval.
Mapsto.
Intro_sepimp h'1 h'.
assert (h2 # h'1 /\
        ((nat_e cur_adr +e int_e 1%Z)
         |-> nat_e (cur_adr + cur_size + 4 + next_size)) s h'1).
split; [Disjoint_heap | idtac].
unfold next in H19.
Mapsto.
generalize (H18 _ H21 _ H20); clear H21 H15 H18.
intros.
exists (l1 ++ ((cur_adr, cur_size + 2 + next_size, Free) :: nil) ++ l2).
split; auto.
split; auto.
rewrite H4 in H6.
generalize (in_app_or _ _ _ H6); intro X; inversion_clear X.
auto with *.
simpl in H18; inversion_clear H18.
inversion H21.
simpl in H21; inversion_clear H21.
inversion H18.
auto with *.
split; auto.
split; auto.
exists cur_adr.
split; auto.
exists (cur_size + 2 + next_size).
split.
auto with *.
split; auto.
rewrite H13; simpl; OmegaZ.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       exists cur_adr, eval (var_e cptr) s = eval (nat_e cur_adr) s /\
       (exists cur_size, 
            In (cur_adr, cur_size, Free) l /\            
            cur_adr > 0 /\
            eval (var_e nptr) s = eval (nat_e (cur_adr + 2 + cur_size)) s
       )
).
inversion_clear H3 as [l].
decompose [and] H4; clear H4.
inversion_clear H9 as [cur_adr].
inversion_clear H4.
inversion_clear H9 as [cur_size].
decompose [and] H4; clear H4.
red.
exists l.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists cur_adr.
split.
Store_update.
exists cur_size.
split; auto.
split; auto.
Store_update.

Step TT.

red; intros.
inversion_clear H3 as [l].
decompose [and] H4; clear H4.
inversion_clear H9 as [cur_adr].
inversion_clear H4.
inversion_clear H9 as [cur_size].
decompose [and] H4; clear H4.

generalize (list_split _ _ _ H9); intros.
inversion_clear H4 as [l1].
inversion_clear H10 as [l2].

induction l2.
simpl in H4.
rewrite H4 in H3.
generalize (Heap_List_last_bloc _ _ _ _ _ _ _ H3); intros.
eapply Heap_List_status_last with (bloc_adr := cur_adr + 2 + cur_size).
omega.
Decompose_sepcon H10 h1 h2.
Compose_sepcon h2 h1; [auto | red; auto].
unfold status.
Simpl_eval.
rewrite H12.
OmegaZ.
red.
exists l.
split.
rewrite H4.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists cur_adr.
split.
Store_update.
exists cur_size.
split; auto.
split.
Store_update.
split; auto.
right.
split.
Decompose_sepcon H10 h1 h2.
Compose_sepcon h1 h2.
rewrite H4; Heap_List_equiv.
Heap_List_equiv.
Store_update.

clear IHl2.
induction a; induction a.
simpl in H4.

assert (a = cur_adr + 2 + cur_size).
rewrite H4 in H3.
eapply Heap_List_next_bloc.
simpl.
apply H3.
subst a.

assert (In (cur_adr + 2 + cur_size, b0, b) l).
rewrite H4.
auto with *.


eapply Heap_List_status.
apply H10.
Compose_sepcon h heap.emp; [apply H3 | red; auto].
Simpl_eval.
unfold status; rewrite H12; OmegaZ.

red.

exists l.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists cur_adr.
split.
Store_update.
exists cur_size.
split; auto.
split.
Store_update.
split; auto.
left.
exists b0; exists b.
split.
rewrite H4.
auto with *.
generalize (Heap_List_block_status _ _ _ _ _ _ _ H3 H10); intro X; inversion_clear X.
subst b.
Store_update.
subst b.
Store_update.

red; intros.
inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10 as [cur_adr].
inversion_clear H3.
inversion_clear H10 as [cur_size].
decompose [and] H3; clear H3.
inversion_clear H14.
exists l.
split; auto.
split; auto.
split; auto.
split; auto.
exists cur_adr.
split; auto.
right.
exists cur_size.
exists Free.
split; auto.

exists l.
split; auto.
split; auto.
split; auto.
split; auto.
exists cur_adr.
split; auto.
inversion_clear H3.
right.
exists cur_size.
exists Free.
split; auto.


Step TT.

red; intros.
inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10 as [cur_adr].
inversion_clear H3.
inversion_clear H10.
inversion_clear H3.
inversion_clear H11.
exists l.
split; auto.
split; auto.
split; auto.
split; auto.
exists cur_adr.
split; auto.
inversion_clear H3 as [cur_size].
inversion_clear H10 as [cur_status].
decompose [and] H3; clear H3.
exists l.
split; auto.
split; auto.
split; auto.
split; auto.
exists cur_adr.
split; auto.
right.
exists cur_size.
exists cur_status.
auto.

Step TT.
red; intros.
inversion_clear H3 as [l].
decompose [and] H4; clear H4.
inversion_clear H9 as [cur_adr].
inversion_clear H4.
inversion_clear H9.
inversion_clear H4.

eapply Heap_List_next_last.
apply H10.
Decompose_sepcon H9 h1 h2.
Compose_sepcon h2 h1.
Heap_List_equiv.
red; auto.
unfold next.
Simpl_eval.
rewrite H8; Omega_exprb.
red.
exists l.
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
left; auto.

inversion_clear H4 as [cur_size].
inversion_clear H9 as [cur_status].
inversion_clear H4.
generalize (list_split _ _ _ H9); intro.
inversion_clear H4 as [l1].
inversion_clear H11 as [l2].
rewrite H4 in H3.
eapply Heap_List_next.
Compose_sepcon h heap.emp.
apply H3.
red; auto.
unfold next; Simpl_eval; rewrite H8; Omega_exprb.
red.
exists (l1 ++ ((cur_adr, cur_size, cur_status) :: nil) ++ l2).
split.
Heap_List_equiv.
split.
rewrite H4 in H6.
auto.
split.
Store_update.
split.
Store_update.
exists (cur_adr + 2 + cur_size).
split.
Store_update.
induction l2.
right; left.

split.
simpl in H3.
generalize (Heap_List_last_bloc _ _ _ _ _ _ _ H3); intro.
Decompose_sepcon H11 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Heap_List_equiv.
omega.
clear IHl2.
right; right.
induction a; induction a.
exists b0; exists b.
split.
simpl in H3.
generalize (Heap_List_next_bloc _ _ _ _ _ _ _ _ _ _ _ H3); intros.
subst a.
auto with *.
omega.

red; intros.
inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
exists l.
auto.
Qed.



Lemma split_verif1 : split_specif1.
unfold split_specif1.
intros.
unfold split.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       (exists finded_free_block : loc,
          (exists size'' : nat,
             size'' >= size /\
             In (finded_free_block, size'', Free) l /\
             eval (var_e entry) s = Z_of_nat finded_free_block /\
             finded_free_block > 0 /\ finded_free_block <> x /\
             eval (var_e sz) s = eval (nat_e size'') s))

).

unfold ENTRYSIZE.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       (exists finded_free_block : loc,
          (exists size'' : nat,
             size'' >= size /\
             In (finded_free_block, size'', Free) l /\
             eval (var_e entry) s = Z_of_nat finded_free_block /\
             finded_free_block > 0 /\ finded_free_block <> x /\
             eval (var_e sz) s = eval (nat_e (finded_free_block + 2 + size'')) s))

).

inversion_clear H3 as [l].
decompose [and] H4; clear H4.
inversion_clear H9 as [finded_free_block].
inversion_clear H4 as [size''].
decompose [and] H8; clear H8.
generalize (list_split _ _ _ H10); intros.
inversion_clear H8 as [l1].
inversion_clear H12 as [l2].
rewrite H8 in H3.
eapply Heap_List_next.
Compose_sepcon h heap.emp.
apply H3.
red; auto.
unfold next.
Simpl_eval.
rewrite H9.
Omega_exprb.
red.
exists l.
split.
rewrite H8.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists finded_free_block.
exists size''.
split; auto.
split; auto.
split.
Store_update.
split; auto.
split; auto.
Store_update.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       (exists finded_free_block : loc,
          (exists size'' : nat,
             size'' >= size /\
             In (finded_free_block, size'', Free) l /\
             eval (var_e entry) s = Z_of_nat finded_free_block /\
             finded_free_block > 0 /\ finded_free_block <> x /\
             eval (var_e sz) s = eval (nat_e size'') s))

).

inversion_clear H3 as [l].
decompose [and] H4; clear H4.
inversion_clear H9 as [finded_free_block].
inversion_clear H4 as [size''].
decompose [and] H8; clear H8.
red.
exists l.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists finded_free_block.
exists size''.
split; auto.
split; auto.
split.
Store_update.
split; auto.
split; auto.
Simpl_eval.
Store_update.

Step TT.

Step TT.
red.
intros.
inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10 as [finded_free_block].
inversion_clear H3 as [size''].
decompose [and] H9; clear H9.
assert (size'' < 0).
Simpl_eval.
Omega_exprb.
inversion H9.

Step TT.
red; intros.
intuition.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       (exists finded_free_block : loc,
          (exists size'' : nat,
             size'' >= size /\
             In (finded_free_block, size'', Free) l /\
             eval (var_e entry) s = Z_of_nat finded_free_block /\
             finded_free_block > 0 /\ finded_free_block <> x 
(*             eval (var_e sz) s = eval (nat_e size'') s*)))

).

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       (exists finded_free_block : loc,
          (exists size'' : nat,
             size'' >= size /\
             In (finded_free_block, size'', Free) l /\
             eval (var_e entry) s = Z_of_nat finded_free_block /\
             finded_free_block > 0 /\ finded_free_block <> x /\
             eval (var_e sz) s = eval (nat_e size'') s /\
             size'' >= size +LEFTOVER + 2 /\
             eval (var_e cptr) s = eval (nat_e (finded_free_block + 2 + size)) s
             ))

).
inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10 as [finded_free_block].
inversion_clear H3 as [size''].
decompose [and] H9; clear H9.
red.
exists l.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists finded_free_block.
exists size''.
split; auto.
split; auto.
split.
Store_update.
split; auto.
split; auto.
split.
Simpl_eval.
Store_update.
split.
unfold LEFTOVER.
Simpl_eval.
Omega_exprb.
Simpl_eval.
Store_update.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       (exists finded_free_block : loc,
          (exists size'' : nat,
             size'' >= size /\
             In (finded_free_block, size'', Free) l /\
             eval (var_e entry) s = Z_of_nat finded_free_block /\
             finded_free_block > 0 /\ finded_free_block <> x /\
             eval (var_e sz) s = eval (nat_e (finded_free_block + 2 + size'')) s /\
             size'' >= size +LEFTOVER + 2 /\
             eval (var_e cptr) s = eval (nat_e (finded_free_block + 2 + size)) s
             ))

).
inversion_clear H3 as [l].
decompose [and] H4; clear H4.
inversion_clear H9 as [finded_free_block].
inversion_clear H4 as [size''].
decompose [and] H8; clear H8.

generalize (list_split _ _ _ H10); intros.
inversion_clear H8 as [l1].
inversion_clear H15 as [l2].
rewrite H8 in H3.
eapply Heap_List_next.
Compose_sepcon h heap.emp.
apply H3.
red; auto.
Simpl_eval.
unfold next.
rewrite H9.
Omega_exprb.

red.
exists l.
split.
rewrite H8.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
exists finded_free_block.
exists size''.
split; auto.
split; auto.
split.
Store_update.
split; auto.
split; auto.
split.
Simpl_eval.
Store_update.
split.
Omega_exprb.
Store_update.

Step ( fun s h => exists e'',
     ((cptr -.> status) |-> e'' **
      ((cptr -.> status) |-> Free -*
       (fun (s0 : store.s) (h0 : heap.h) =>
        exists e''0 : expr,
          ((entry -.> next) |-> e''0 **
           ((entry -.> next) |-> var_e cptr -*
            (fun (s1 : store.s) (h1 : heap.h) =>
             exists l : list (loc * nat * expr),
               Heap_List l adr 0 s1 h1 /\
               In (x, sizex, Allocated) l /\
               eval (var_e hmStart) s1 = eval (nat_e adr) s1 /\
               eval (var_e result) s1 = eval null s1 /\
               (exists finded_free_block : loc,
                  (exists size'' : nat,
                     size'' >= size /\
                     In (finded_free_block, size'', Free) l /\
                     eval (var_e entry) s1 = Z_of_nat finded_free_block /\
                     finded_free_block > 0 /\
                     finded_free_block <> x 
(*                     eval (var_e sz) s1 = eval (nat_e size'') s1*)

                     ))))) s0 h0)))
       s h
)
.
inversion_clear H3 as [l].
decompose [and] H4; clear H4.
inversion_clear H9 as [finded_free_block]. 
inversion_clear H4 as [size''].
decompose [and] H8; clear H8.

generalize (list_split _ _ _ H10); intros.
inversion_clear H8 as [l1].
inversion_clear H15 as [l2].
subst l.

assert (exists size_split, size'' = size + 2 + size_split).
exists (size'' - 2 - size).
omega.
inversion_clear H8 as [size_split].
subst size''.

generalize (Splitting _ _ _ _ _ _ _ _ H1 H3).
intros.
inversion_clear H8 as [e1].
Decompose_sepcon H15 h1 h2.
exists e1.
Compose_sepcon h1 h2.
unfold next.
Simpl_eval.
Mapsto.
rewrite H16.
Omega_exprb.
Intro_sepimp h'1 h'.

assert ( h2 # h'1 /\  (nat_e (finded_free_block + 3 + size)  |-> nat_e (finded_free_block + 4 + size + size_split)) s h'1).
split; auto.
Simpl_eval.
Mapsto.
unfold next.
rewrite H16.
Omega_exprb.
clear H15.
generalize (H19 _ H22 _ H21); intro; clear H19 H22.

inversion_clear H15 as [e2].
Decompose_sepcon H19 h1' h2'.
exists e2.
Compose_sepcon h1' h2'.
unfold status.
Simpl_eval.
Mapsto.
Intro_sepimp h'1' h''.

assert ( h2' # h'1' /\  (nat_e (finded_free_block + 2 + size) |-> Free) s h'1').
split; auto.
Simpl_eval.
Mapsto.
unfold status.
rewrite H16.
Omega_exprb.
generalize (H24 _ H27 _ H26); intro; clear H27 H24.

inversion_clear H28 as [e3].
Decompose_sepcon H24 h1'' h2''.
exists e3.
Compose_sepcon h1'' h2''.
unfold next.
Simpl_eval.
Mapsto.
Intro_sepimp h'1'' h'''.

assert ( h2'' # h'1'' /\  (nat_e (finded_free_block + 1) |-> nat_e (finded_free_block + 2 + size)) s h'1'').
split; auto.
Simpl_eval.
Mapsto.
unfold next.
rewrite H9.
Omega_exprb.
generalize (H30 _ H33 _ H32); intro; clear H33 H30.

exists (l1 ++
           ((finded_free_block, size, Free)
            :: (finded_free_block + 2 + size, size_split, Free) :: nil) ++ l2).

split.

auto.
split.

generalize (in_app_or _ _ _ H6); intro X; inversion_clear X.

eapply in_or_app.
left; auto.
simpl in H30.
inversion_clear H30.
inversion H33.
eapply in_or_app.
right.
simpl.
tauto.
split; auto.
split; auto.
exists finded_free_block.
exists size.
split; auto.
split.
auto with *.
split; auto.


Step (

(
(fun s0 h0 => exists e'',
      ((entry -.> next) |-> e'' **
       ((entry -.> next) |-> var_e cptr -*
        (fun (s : store.s) (h : heap.h) =>
         exists l : list (loc * nat * expr),
           Heap_List l adr 0 s h /\
           In (x, sizex, Allocated) l /\
           eval (var_e hmStart) s = eval (nat_e adr) s /\
           eval (var_e result) s = eval null s /\
           (exists finded_free_block : loc,
              (exists size'' : nat,
                 size'' >= size /\
                 In (finded_free_block, size'', Free) l /\
                 eval (var_e entry) s = Z_of_nat finded_free_block /\
                 finded_free_block > 0 /\
                 finded_free_block <> x 
(*                 eval (var_e sz) s = eval (nat_e size'') s*)))))) s0 h0)
)

).

auto.

Step TT.
red; auto.


Step TT.
red; intros.
inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10.
inversion_clear H3.
decompose [and] H9; clear H9.
exists l.
split; auto.
split; auto.
split; auto.
split; auto.
exists x0; exists x1.
split; auto.

Step TT.
red; intros.
inversion_clear H3 as [l].
decompose [and] H4; clear H4.
inversion_clear H9 as [finded_free_block].
inversion_clear H4 as [size''].
decompose [and] H8; clear H8.
generalize (list_split _ _ _ H10); intro.
inversion_clear H8 as [l1].
inversion_clear H12 as [l2].
rewrite H8 in H3.
generalize (change_status_Free_to_Alloc  _ _ _ _ _ _ _ H1 H3); intros.
inversion_clear H12.
Decompose_sepcon H14 h1 h2.
exists x0.
Compose_sepcon h1 h2.
unfold status.
Simpl_eval.
Mapsto.
Intro_sepimp h'1 h'.
assert (h2 # h'1 /\ (nat_e finded_free_block |-> Allocated) s h'1).
split.
Disjoint_heap.
unfold status in H18.
Simpl_eval.
Mapsto.
generalize (H17 h'1 H20 h' H19); intros.
exists ((l1 ++ ((finded_free_block, size'', Allocated) :: nil) ++ l2)).
split.

rewrite H8 in H6.
generalize (in_app_or _ _ _ H6); intro X; inversion_clear X.
intuition.
simpl in H22; inversion_clear H22.
inversion H23.
intuition.

exists finded_free_block.
split; auto.
split.
auto.
exists size''.
split; auto.
split.
Decompose_sepcon H21 h1' h2'.
Compose_sepcon h1' h2'.
auto.
auto.
intuition.
Qed.

Lemma hmAlloc_verif1: hmAlloc_specif1.
unfold hmAlloc_specif1.
intros.
unfold hmAlloc.

Step (fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s
).

inversion_clear H3 as [l].
decompose [and] H4; clear H4.
red.
exists l.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
Store_update.

assert (var.set (hmStart :: entry :: fnd :: sz :: stts :: result :: nil)).
simpl.
simpl in H.
intuition.
generalize (findFree_verif1 adr entry fnd sz stts size sizex x result H2 H1 H0 H3); clear H3; intros.

Step TT.
red; auto.
clear H3.

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       ((exists finded_free_block : loc,
           (exists size'' : nat,
              size'' >= size /\
              In (finded_free_block, size'', Free) l /\
              eval (var_e entry) s = Z_of_nat finded_free_block /\
              finded_free_block > 0)) \/ eval (var_e entry) s = eval null s)

).

Step (

fun s h => exists l,
       Heap_List l adr 0 s h /\
       In (x, sizex, Allocated) l /\
       eval (var_e hmStart) s = eval (nat_e adr) s /\
       eval (var_e result) s = eval null s /\
       eval (var_e entry) s = eval null s /\
       eval (var_e cptr) s = eval (var_e hmStart) s

).
inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10.

inversion_clear H3 as [finded_free_block].
inversion_clear H9 as [size''].
decompose [and] H3; clear H3.
assert (eval (var_e entry) s = 0%Z).
Omega_exprb.
assert (eval (var_e entry) s <> 0%Z).
Omega_exprb.
contradiction.
red.
exists l.
split.
Heap_List_equiv.
split; auto.
split.
Store_update.
split.
Store_update.
split.
Store_update.
Store_update.

assert (var.set (hmStart :: entry :: cptr :: nptr :: stts :: result :: nil)).
simpl.
simpl in H.
intuition.

generalize (compact_verif1 adr cptr nptr stts size sizex x result entry H2 H1 H0 H3); clear H3; intros.

Step TT.
red; intros.
inversion_clear H4.
exists x0.
intuition.

clear H3.

assert (var.set (hmStart :: entry :: fnd :: sz :: stts :: result :: nil)).
simpl.
simpl in H.
intuition.
generalize (findFree_verif1 adr entry fnd sz stts size sizex x result H2 H1 H0 H3); clear H3; intros.
Step TT.
red; auto.
red; auto.

Step TT.
red; intros.
inversion_clear H3.
inversion_clear H4 as [l].
exists l.
decompose [and] H3; clear H3.
split; auto.

Step TT.

Step TT.
red; intros.
inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
red.
inversion_clear H10.

inversion_clear H3 as [finded_free_block].
inversion_clear H9 as [size''].
decompose [and] H3; clear H3.
assert (eval (var_e entry) s = 0%Z).
Omega_exprb.
assert (eval (var_e entry) s <> 0%Z).
Omega_exprb.
contradiction.
right.
exists l.
split.
Store_update.
split.
Heap_List_equiv.
auto.

assert (var.set (hmStart :: entry :: cptr :: sz :: result :: nil)).
simpl.
simpl in H.
intuition.
generalize (split_verif1 adr cptr sz size sizex x result entry H2 H1 H0 H3); clear H3; intros.

Step (

fun s h => exists l,
           In (x, sizex, Allocated) l /\
           (exists y : nat,
              y > 0 /\
              eval (var_e entry) s = Z_of_nat y /\
              (exists size'' : nat,
                 size'' >= size /\
                 (Heap_List l adr 0 ** Array (y + 2) size'') s h /\
                 In (y, size'', Allocated) l /\ y <> x))

).

clear H3.
red; intros.
inversion_clear H3.
inversion_clear H4 as [l].
decompose [and] H3; clear H3.
inversion_clear H10.
inversion_clear H3 as [finded_free_block].
inversion_clear H9 as [size''].
decompose [and] H3; clear H3.
exists l.
split; auto.
split; auto.
split; auto.
split; auto.
exists finded_free_block.
exists size''.
split; auto.
split; auto.
split; auto.
split; auto.

red; intros.
subst x.
generalize (Heap_List_bloc_unique _ _ _ _ _ _ _ _ _ H4 H7 H11); intros.
inversion_clear H3.
inversion H12.
assert (eval (var_e entry) s <> eval null s).
Omega_exprb.
contradiction.

clear H3.

Step TT.
red; intros.
inversion_clear H3 as [l].
red.
left.
decompose [and] H4; clear H4.
inversion_clear H5 as [y].
decompose [and] H4; clear H4.
inversion_clear H8 as [size''].
decompose [and] H4; clear H4.
exists l.
exists y.
split; auto.
split.
Store_update.
exists size''.
split; auto.
split.
Decompose_sepcon H9 h1 h2.
Compose_sepcon h1 h2.
Heap_List_equiv.
Array_equiv.
auto.
Qed.

