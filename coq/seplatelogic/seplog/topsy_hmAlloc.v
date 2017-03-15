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

Require Import topsy_hm.

Require Import Bool.

(***************************************************************************)

(*
 * this file contains:
 * 1. the verification of list traversal (findFree)
 * 2. the verification of compaction (compact, original version and optimization)
 * 3. the verification of splitting (split)
 * 4. the verification of the allocation function (hmAlloc)
*)

(****************************************************************************)

(*
140 #define ENTRYSIZE(ptr) ((unsigned long)(ptr->next) - \
141                         (unsigned long)ptr - sizeof(HmEntryDesc))
142 
*)
Definition ENTRYSIZE (x:var.v) (tmp:var.v) := 
  tmp <-* (x -.> next);
  tmp <- (var_e tmp -e var_e x -e int_e 2%Z);
  ifte (nat_e 0 >> var_e tmp) thendo 
    tmp <- nat_e 0
  elsedo 
    skip.

(*
144 static HmEntry findFree(unsigned long size)
145 {
146     HmEntry entry = start;
147     
148     while (entry != NULL) {
149         if (entry->status == HM_FREED && ENTRYSIZE(entry) >= size) break;
150         entry = entry->next;
151     }
152     return entry;
153 }
*)
Definition findFree (size:nat) (entry fnd sz stts:var.v) :=
  entry <- var_e hmStart;
  stts <-* (entry -.> status);
  fnd <- int_e 0%Z;
  while ((var_e entry =/= null) &&& (var_e fnd =/= int_e 1%Z)) (
    stts <-* (entry -.> status);
    ENTRYSIZE entry sz;
    ifte ((var_e stts == Free) &&& (var_e sz >>= nat_e size)) thendo 
      (fnd <- int_e 1%Z)
    elsedo 
      (entry <-* (entry -.> next))).

(*
170 static void compact(HmEntry at)
171 {
172     HmEntry atNext;
173 
174     while (at != NULL) {
175         atNext = at->next;
176         while ((at->status == HM_FREED) && (atNext != NULL)) {
177             if (atNext->status != HM_FREED) break;
178             at->next = atNext->next;     /* collapse two free entries into one */
179             atNext = atNext->next;
180         }
181         at = at->next;
182     }
183 }
184
*)
Definition LEFTOVER : nat := 8.

(* original version *)
Definition compact' (cptr nptr brk tmp cstts nstts:var.v) :=
  while (var_e cptr =/= null) (
    nptr <-* (cptr -.> next);
    brk <- nat_e 1 ;
    cstts <-* (cptr -.> status);
    while ((var_e cstts == Free) &&& (var_e nptr =/= null) &&& (var_e brk == nat_e 1)) (
       nstts <-* (nptr -.> status);
       ifte (var_e nstts =/= Free) thendo (
          brk <- nat_e 0
       ) elsedo (
	 tmp <-* nptr -.> next;
         cptr -.> next *<- var_e tmp ;
(*         nptr <-* nptr -.> next*)
         nptr <- (var_e tmp)
       )
    );
    cptr <-* (cptr -.> next)
  ).

(* optimized version *)
Definition compact (cptr nptr stts:var.v) :=
  while (var_e cptr =/= null) (
    stts <-* (cptr -.> status);
    ifte (var_e stts ==  Free) thendo (
      nptr <-* (cptr -.> next); 
      stts <-* (nptr -.> status);
      while (var_e stts == Free) (

        stts <-* (nptr -.> next);
        (cptr -.> next) *<- var_e stts;
        nptr <- var_e stts;
        stts <-* (nptr -.> status))) 
    elsedo 
      skip;
      cptr <-* (cptr -.> next)).

(*
156 static void split(HmEntry entry, unsigned long int size)
157 {
158     HmEntry new;
159     
160     if (ENTRYSIZE(entry) >= (size + sizeof(HmEntryDesc) + LEFTOVER)) {
161         new = (HmEntry)((unsigned long)(entry) + sizeof(HmEntryDesc) + size);
162         new->next = entry->next;
163         new->status = HM_FREED;
164         entry->next = new;
165     }
166     entry->status = HM_ALLOCATED;
167 }
168 
*)
(* entry contains the address of a free entry, size is the size we want to allocated *)
Definition split (entry:var.v) (size:nat) (cptr sz:var.v) :=
  ENTRYSIZE entry sz;
  ifte (var_e sz >>= (nat_e size +e nat_e LEFTOVER +e nat_e 2)) thendo (
    cptr <- var_e entry +e nat_e 2 +e nat_e size;
    sz <-* (entry -.> next);
    (cptr -.> next) *<- var_e sz;
    (cptr -.> status) *<- Free;
    (entry -.> next) *<- var_e cptr) 
   elsedo 
     skip
  ;
  (entry -.> status) *<- Allocated.

(*
162 Error hmAlloc(Address* addressPtr, unsigned long int size)
163 {
164     HmEntry entry;
165 
166     if (size == 4) 
167       WARNING("Four bytes allocated. Possible pointer problem?");
168 
169     size = size + (ALIGN - size % ALIGN);   /* round up to multiple of words */
170     entry = start;
171     *addressPtr = NULL;
172 
173     /*** here we enter a critical section */
174     lock(hmLock);
175     
176     /* try to find a free piece of memory */
177     entry = findFree(size);
178     if (entry == NULL) {
179         /* compact and try again */
180         compact(start);
181         entry = findFree(size); 
182     } 
183     if (entry == NULL) {
184         unlock( hmLock);
185         return HM_ALLOCFAILED;
186     }
187     split(entry, size);
188     *addressPtr = (Address)((unsigned long)entry + sizeof(HmEntryDesc));
189 
190     unlock(hmLock);    
191     return HM_ALLOCOK;
192 }
*)
Definition HM_ALLOCFAILED := int_e 0%Z.

Definition HM_ALLOCOK := int_e 1%Z.

Definition hmAlloc (result:var.v) (size: nat) (entry:var.v) (cptr fnd stts nptr sz:var.v) :=
  (* alignment calculus ignored (not relevant to verification) *)
  (* entry <- var_e hmStart;*) (* useless insn *)
  result <- null;
  findFree size entry fnd sz stts;
  ifte (var_e entry == null) thendo (
    cptr <- var_e hmStart;
    compact cptr nptr stts;
    findFree size entry fnd sz stts
  ) elsedo
    skip
  ;
  ifte (var_e entry == null) thendo (
    result <- HM_ALLOCFAILED
  ) elsedo (
    split entry size cptr sz;
    result <- var_e entry +e nat_e 2
  ).

(***************************************************************************)

Ltac Resolve_topsy :=
  match goal with
    | id: Heap_List ?l ?adr ?s1 ?h |-
            Heap_List ?l ?adr ?s2 ?h =>
                    eapply Heap_List_inde_store; apply id
    | |- (?s |b= ?b) =>
            (
              (rewrite <- expr_b_store_update_rewrite; Omega_exprb) ||
              Omega_exprb
            )
    | |- ?P /\ ?Q => split; Resolve_topsy
    | |- _ => auto
  end.

(****************************************************************************)

Definition findFree_specif := forall adr x sizex size,
  size > 0 -> adr > 0 ->
  {{ fun s h => exists l,  Heap_List l adr s h /\ 
     In_hl l (x,sizex,alloc) adr /\
     (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) }}
  findFree size entry fnd sz stts
  {{ fun s h => exists l, Heap_List l adr s h /\ 
     In_hl l (x,sizex,alloc) adr /\
     (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\    
     ((exists y, exists size'', size'' >= size /\ 
      In_hl l (y,size'',free) adr /\ 
      (s |b= (var_e entry == nat_e y) &&& (nat_e y >> null)))
      \/
      s |b= var_e entry == null) }}.

Lemma findFree_verif : findFree_specif.
unfold findFree_specif.
intros.
unfold findFree.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= var_e hmStart == (nat_e adr)) /\
       (s |b= var_e result == null) /\
       (s |b= var_e entry == (nat_e adr))
).

red.
Decompose_hyp.
exists x0.
split.
eapply Heap_List_inde_store; apply H1.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= (var_e hmStart) == (nat_e adr)) /\
       (s |b= (var_e result) == null) /\
       (s |b= (var_e entry) == (nat_e adr)) /\
       (s |b= ((var_e stts) == Allocated) ||| ((var_e stts) == Free))       
).

Decompose_hyp.
unfold status.
destruct x0.
simpl in H4; contradiction.
destruct p.
exists (hlstat_bool2expr b).
eapply cell_read.
split.
Decompose_sepcon H1 h1 h2.
inversion_clear H2.
subst b; subst next.
Decompose_sepcon H13 h31 h32.
Decompose_sepcon H11 h311 h312.
Compose_sepcon h311 (h312 +++ h32 +++ h4 +++ h2).
Mapsto.
red; auto.
subst b; subst next.
Decompose_sepcon H13 h31 h32.
Compose_sepcon h31 (h32 +++ h4 +++ h2).
Mapsto.
red; auto.
red.
exists ((n,b)::x0).
split.
eapply Heap_List_inde_store; apply H1.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
destruct b; rewrite <- expr_b_store_update_rewrite; Omega_exprb.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= var_e hmStart == nat_e adr) /\
       (s |b= var_e result == null) /\
       (s |b= var_e entry == (nat_e adr)) /\
       (s |b= ((var_e stts) == Allocated) ||| ((var_e stts) == Free)) /\
       (s |b= (var_e fnd) == nat_e 0)
).

Decompose_hyp.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H1.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split; rewrite <- expr_b_store_update_rewrite; Omega_exprb.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= (var_e hmStart) == (nat_e adr)) /\
       (s |b= var_e result == null) /\
       (exists bloc_adr, 
         (s |b= (var_e entry) == (nat_e bloc_adr)) /\
         (
           (bloc_adr = 0 /\ (s |b= (var_e fnd) == (nat_e 0))) \/
           (bloc_adr = get_endl l adr  /\
           (s |b= (var_e fnd) == nat_e 0) /\
            bloc_adr > 0) \/
           (exists bloc_size, exists bloc_status,
            bloc_adr > 0 /\
            In_hl l (bloc_adr, bloc_size, bloc_status) adr /\ 
            (s |b= (var_e fnd) == nat_e 0)
           ) \/
           (exists bloc_size, bloc_size >= size /\
            In_hl l (bloc_adr, bloc_size, free) adr /\ 
            (s |b= (var_e fnd) == nat_e 1) /\
            bloc_adr >0)))      
).

red; intros.
Decompose_hyp.
exists x0.
split; auto.
split; auto.
split; auto.
split; auto.
destruct x0.
simpl in H4; contradiction.
destruct p.
exists adr.
split.
Omega_exprb.
right.
right; left.
exists n; exists b.
split; auto.
split.
simpl.
repeat rewrite <- beq_nat_refl.
repeat rewrite bool_eq_refl.
simpl; auto.
auto.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= var_e hmStart == (nat_e adr)) /\
       (s |b= var_e result == null) /\
       (exists bloc_adr, 
         (s |b= (var_e entry) ==nat_e bloc_adr) /\
         (
           (bloc_adr = get_endl l adr /\
            (s |b= (var_e fnd) == nat_e 0) /\
            (s |b= (var_e stts) == Allocated) /\
            bloc_adr > 0) \/
           (exists bloc_size, exists bloc_status, 
            In_hl l (bloc_adr, bloc_size, bloc_status) adr /\ 
            (s |b= (var_e fnd) == nat_e 0) /\
            (s |b= (var_e stts) == (hlstat_bool2expr bloc_status)) /\
            bloc_adr > 0)))      
).

Decompose_hyp.
inversion_clear H8.
Decompose_hyp.
subst x1.
Omega_exprb.
inversion_clear H1.
Decompose_hyp.
subst x1.
exists Allocated.
apply cell_read.
split.
generalize (hl_getstat' _ _ _ _ H2); intros.
Decompose_hyp.
unfold status.
Compose_sepcon H8 H1.
Mapsto.
red; auto.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H2.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
exists (get_endl x0 adr).
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
left.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
auto.

inversion_clear H8.
Decompose_hyp.
generalize (In_hl_destruct _ _ _ _ _ H10); intros.
Decompose_hyp.
exists (hlstat_bool2expr x3).
unfold status.
apply cell_read.
split.
rewrite H9 in H2.
generalize (hl_getstatus _ _ _ _ _ _ _ H2); intros.
Decompose_sepcon H1 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H2.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
exists (get_endl x4 adr).
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
right.
exists x2.
exists x3.
split.
rewrite <- H12 in H10.
auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite.
destruct x3; Omega_exprb.
generalize (get_endl_gt x4 adr); intros.
omega.

Decompose_hyp.
generalize (In_hl_destruct _ _ _ _ _ H10); intros.
Decompose_hyp.
exists (Free).
unfold status.
apply cell_read.
split.
rewrite H11 in H2.
generalize (hl_getstatus _ _ _ _ _ _ _ H2); intros.
Decompose_sepcon H8 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H2.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
exists (get_endl x3 adr).
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
right.
exists x2.
exists free.
split.
rewrite <- H13 in H10.
auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
generalize (get_endl_gt x3 adr); intros.
omega.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= var_e hmStart == (nat_e adr)) /\
       (s |b= var_e result == null) /\
       (exists bloc_adr, 
         (s |b= (var_e entry) == (nat_e bloc_adr)) /\
         (
           (bloc_adr = get_endl l adr /\
            (s |b= (var_e fnd) == (nat_e 0)) /\
            (s |b= (var_e stts) == Allocated) /\
            bloc_adr > 0 /\
            (s |b= (var_e sz) == nat_e 0)) \/
           (exists bloc_size, exists bloc_status,
            In_hl l (bloc_adr, bloc_size, bloc_status) adr /\ 
            (s |b= (var_e fnd) == nat_e 0) /\
            (s |b= (var_e stts) == (hlstat_bool2expr bloc_status)) /\
            bloc_adr > 0 /\
            (s |b= (var_e sz) == nat_e bloc_size)
           )
         )         
       )      
).

unfold ENTRYSIZE.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= (var_e hmStart) == (nat_e adr)) /\
       (s |b= (var_e result) == null) /\
       (exists bloc_adr, 
         (s |b= (var_e entry) == (nat_e bloc_adr)) /\
         ((bloc_adr = get_endl l adr /\
            (s |b= (var_e fnd) == (nat_e 0)) /\
            (s |b= (var_e stts) == Allocated) /\
            bloc_adr > 0 /\
            (s |b= (var_e sz) == nat_e 0)) \/
           (exists bloc_size, exists bloc_status, 
            In_hl l (bloc_adr, bloc_size, bloc_status) adr /\ 
            (s |b= (var_e fnd) == nat_e 0) /\
            (s |b= (var_e stts) == (hlstat_bool2expr bloc_status)) /\
            bloc_adr > 0 /\
            (s |b= (var_e sz) == (nat_e (bloc_adr + 2 + bloc_size)))
           )
         )         
       )      
).

Decompose_hyp.
inversion_clear H7.
Decompose_hyp.

exists null.
unfold next.
apply cell_read.
split.
generalize (hl_getnext' _ _ _ _ H1); intros.
Decompose_sepcon H2 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H1.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
exists x1.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
left.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split; auto.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.

Decompose_hyp.
generalize (In_hl_destruct _ _ _ _ _ H7); intros.
Decompose_hyp.
exists (nat_e (x1 + 2 + x2)).
unfold next.
apply cell_read.
split.
rewrite H10 in H1.
generalize (hl_getnext _ _ _ _ _ _ _ H1); intros.
Decompose_sepcon H2 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H1.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
exists (get_endl x4 adr).
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
right.
exists x2.
exists x3.
split.
rewrite <- H12 in H7.
auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite.
destruct x3; Omega_exprb.
split; auto.
generalize (get_endl_gt x4 adr); intros.
omega.
rewrite <- expr_b_store_update_rewrite.
destruct x3; Omega_exprb.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= var_e hmStart == nat_e adr) /\
       (s |b= var_e result == null) /\
       (exists bloc_adr, 
         (s |b= (var_e entry) == (nat_e bloc_adr)) /\
         (
           (bloc_adr = get_endl l adr /\
            (s |b= (var_e fnd) == nat_e 0) /\
            (s |b= (var_e stts) == Allocated) /\
            bloc_adr > 0 /\
            (s |b= (var_e sz) == (nat_e 0 -e nat_e bloc_adr -e nat_e 2))) \/
           (exists bloc_size, exists bloc_status, 
            In_hl l (bloc_adr, bloc_size, bloc_status) adr /\ 
            (s |b= (var_e fnd) == nat_e 0) /\
            ((s |b= (var_e stts) == (hlstat_bool2expr bloc_status))) /\
            bloc_adr > 0 /\
            ((s |b=  (var_e sz) == (nat_e bloc_size)))
           )))      
).

Decompose_hyp.
inversion_clear H7.
Decompose_hyp.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H1.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
exists (get_endl x0 adr).
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
left.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
generalize (get_endl_gt x0 adr); intros.
omega.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.

Decompose_hyp.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H1.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
exists x1.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
right.
exists x2.
exists x3.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite.
destruct x3; Omega_exprb.
split; auto.
rewrite <- expr_b_store_update_rewrite.
simpl expr_b_rewrite.
simpl.
simpl in H12.
generalize (Zeq_bool_true _ _ H12); intros.
cutrewrite (store.lookup sz s - store.lookup entry s - 2 = Z_of_nat x2)%Z.
apply Zeq_bool_refl.
rewrite H2.
simpl in H6.
generalize (Zeq_bool_true _ _ H6); intros.
rewrite H11.
OmegaZ.

Step TT.

Step TT.

intros.
Decompose_hyp.
inversion_clear H8.
Decompose_hyp.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H2.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
exists x1.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
left.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split; auto.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.

Decompose_hyp.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H2.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
exists x1.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
right.
exists x2; exists x3.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split; auto.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.

Step TT.
red; intros; Decompose_hyp.
exists x0.
split; auto.
split; auto.
split.
Omega_exprb.
split.
Omega_exprb.
inversion_clear H8.
Decompose_hyp.
assert (s |b= nat_e 0 >> var_e sz).
Omega_exprb.
Omega_exprb.
exists x1.
split.
Omega_exprb.
right.
trivial.

Step TT.

Step TT.

intros.
Decompose_hyp.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H2.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
exists x1.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
inversion_clear H8.
Decompose_hyp.
assert (s |b= Allocated == Free).
Omega_exprb.
intuition.
Decompose_hyp.
destruct x3.
simpl hlstat_bool2expr in H8.
right; right.
right.
exists x2.
split.
Omega_exprb.
split; auto.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
assert (s |b= Allocated == Free).
Omega_exprb.
simpl in H2.
unfold Zeq_bool in H2.
simpl in H1.
inversion H1.

Step TT.

red; intros.
Decompose_hyp.
unfold next.
inversion_clear H8.
Decompose_hyp.
exists (nat_e 0).
apply cell_read.
split.
generalize (hl_getnext' _ _ _ _ H2); intros.
Decompose_sepcon H1 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H2.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
exists 0.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
left.
split; auto.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
Decompose_hyp.

exists (nat_e (x1 + 2 +x2)).
apply cell_read.
split.
generalize (In_hl_destruct _ _ _ _ _ H8); intros.
Decompose_hyp.
rewrite H12 in H2.
generalize (hl_getnext _ _ _ _ _ _ _ H2); intros.
Decompose_sepcon H1 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H2.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
exists (x1 + 2 + x2).
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
generalize (In_hl_destruct _ _ _ _ _ H8); intros.
Decompose_hyp.
destruct x5.
right; left.
split.
rewrite H12.
rewrite get_endl_app.
simpl.
omega.
split.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.
omega.
destruct p.
right; right; left.
exists n; exists b.
split.
omega.
split.
rewrite H12.
apply In_hl_or_app.
right.
rewrite H14.
simpl.
assert (beq_nat x1 (x1 + 2 + x2) = false).
apply beq_dif_false.
omega.
rewrite H1; simpl.
repeat rewrite <- beq_nat_refl.
rewrite bool_eq_refl.
simpl.
auto.
rewrite <- expr_b_store_update_rewrite; Omega_exprb.

red; intros.
Decompose_hyp.
exists x0.
split; auto.
split; auto.
split; auto.
Omega_exprb.
inversion_clear H8.
Decompose_hyp.
subst x1.
right.
auto.
inversion_clear H1.
Decompose_hyp.
generalize (get_endl_gt x0 adr); intros.
assert (s |b= (var_e entry =/= null) &&& (var_e fnd =/= int_e 1%Z)).
Omega_exprb.
Omega_exprb.
inversion_clear H8.
Decompose_hyp.
generalize (get_endl_gt x0 adr); intros.
assert (s |b= (var_e entry =/= null) &&& (var_e fnd =/= int_e 1%Z)).
Omega_exprb.
Omega_exprb.
Decompose_hyp.
left.
exists x1; exists x2.
split; auto.
split; auto.
Omega_exprb.
Qed.

(****************************************************************************)

Definition brk := 10.
Hint Unfold brk.
Definition tmp := 11.
Hint Unfold tmp.
Definition cstts := 12.
Hint Unfold cstts.
Definition nstts := 13.
Hint Unfold nstts.

Definition compact'_specif:= forall adr size x sizex,
  size > 0 -> adr > 0 ->
  {{ fun s h => exists l, Heap_List l adr s h /\ 
     In_hl l (x,sizex,alloc) adr /\ (s |b= (var_e hmStart == nat_e adr) &&& 
     (var_e result == null) &&& (var_e cptr == nat_e adr)) }}
  compact' cptr nptr brk tmp cstts nstts
  {{ fun s h => exists l, Heap_List l adr s h /\ 
     In_hl l (x,sizex,alloc) adr /\ 
     (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) }}.

Lemma compact'_verif: compact'_specif.
unfold compact'_specif.
intros.
generalize True; intro H1. (* TODO: removeme *)
unfold compact'.

Step (fun s h => exists l, Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
      (exists cptr_value, (s |b= var_e cptr == nat_e cptr_value) /\
      (cptr_value = 0 \/
       cptr_value = get_endl l adr \/
       (exists cptr_size, exists cptr_status, In_hl l (cptr_value,cptr_size,cptr_status) adr)
      ))
).

red; intros.
Decompose_hyp.
exists x0.
Resolve_topsy.
exists adr.
Resolve_topsy.
destruct x0.
simpl in H5; contradiction.
destruct p.
right; right.
exists n; exists b.
simpl.
rewrite bool_eq_refl.
repeat rewrite <- beq_nat_refl.
simpl; auto.

Step (fun s h => exists l, Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
      (exists cptr_value, exists nptr_value, 
        (s |b= var_e cptr == nat_e cptr_value) /\
        (s |b= var_e nptr == nat_e nptr_value) /\
           ((cptr_value = get_endl l adr /\
             nptr_value = 0) \/
            (exists cptr_size, exists cptr_status, 
               In_hl l (cptr_value,cptr_size,cptr_status) adr /\
               nptr_value = cptr_value + 2 + cptr_size
            )))
).

Decompose_hyp.
inversion_clear H8.
assert (s |b= var_e cptr == null).
Omega_exprb.
Omega_exprb.
inversion_clear H2.
unfold next.
exists (nat_e 0).
apply cell_read.
split.
generalize (hl_getnext' _ _ _ _ H3); intros.
Decompose_sepcon H2 h1 h2.
Compose_sepcon h1 h2; [Mapsto | red; auto].
red.
exists x0.
Resolve_topsy.
exists x1.
exists 0.
Resolve_topsy.
Decompose_hyp.
unfold next.
exists (nat_e (x1 + 2 + x2)).
apply cell_read.
split.
generalize (In_hl_destruct _ _ _ _ _ H8); intros.
Decompose_hyp.
rewrite H9 in H3.
generalize (hl_getnext _ _ _ _ _ _ _ H3); intros.
Decompose_sepcon H2 h1 h2.
Compose_sepcon h1 h2; [Mapsto | red; auto].
red.
exists x0.
Resolve_topsy.
exists x1.
exists (x1 + 2 + x2).
Resolve_topsy.
right.
exists x2; exists x3.
Resolve_topsy.

Step (fun s h => exists l, Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null) &&& (var_e brk == (nat_e 1))) /\
      (exists cptr_value, exists nptr_value, 
        (s |b= var_e cptr == (nat_e cptr_value)) /\
        (s |b= var_e nptr == (nat_e nptr_value)) /\
           ((cptr_value = get_endl l adr /\
             nptr_value = 0) \/
            (exists cptr_size, exists cptr_status, 
               In_hl l (cptr_value,cptr_size,cptr_status) adr /\
               nptr_value = cptr_value + 2 + cptr_size
            )
           )
      )
).

Decompose_hyp.
red.
exists x0.
Resolve_topsy.
exists x1; exists x2.
Resolve_topsy.

Step (fun s h => exists l, Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null) &&& (var_e brk == (nat_e 1))) /\
      (exists cptr_value, exists nptr_value, exists cstts_value,
        (s |b= var_e cptr == (nat_e cptr_value)) /\
        (s |b= var_e nptr == (nat_e nptr_value)) /\
        (s |b= var_e cstts == cstts_value) /\
           ((cptr_value = get_endl l adr /\
             nptr_value = 0 /\
             cstts_value = Allocated) \/
            (exists cptr_size, exists cptr_status, 
               In_hl l (cptr_value,cptr_size,cptr_status) adr /\
               nptr_value = cptr_value + 2 + cptr_size /\
               cstts_value = (hlstat_bool2expr cptr_status)
            )))
).

Decompose_hyp.
unfold status.
inversion_clear H9.
Decompose_hyp.
exists Allocated.
apply cell_read.
split.
generalize (hl_getstat' _ _ _ _ H2); intros.
Decompose_sepcon H6 h1 h2.
Compose_sepcon h1 h2; [Mapsto | red; auto].
red.
exists x0.
Resolve_topsy.
exists x1; exists x2.
exists Allocated.
Resolve_topsy.
Decompose_hyp.
exists (hlstat_bool2expr x4).
apply cell_read.
split.
generalize (In_hl_destruct _ _ _ _ _ H7); intros.
Decompose_hyp.
rewrite H10 in H2.
generalize (hl_getstatus _ _ _ _ _ _ _ H2); intros.
Decompose_sepcon H6 h1 h2.
Compose_sepcon h1 h2; [Mapsto | red; auto].
red.
exists x0.
Resolve_topsy.
exists x1; exists x2; exists (hlstat_bool2expr x4).
Resolve_topsy.
destruct x4; Resolve_topsy.
right.
exists x3; exists x4.
Resolve_topsy.

Step (fun s h => exists l, Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
     (
      (exists cptr_value, exists cptr_size, exists brk_value,
        (s |b= var_e cptr == (nat_e cptr_value)) /\
        (s |b= var_e nptr == (nat_e (cptr_value + 2 + cptr_size))) /\
        (s |b= var_e cstts == Free) /\
        (s |b= var_e brk == (nat_e brk_value)) /\
        In_hl l (cptr_value,cptr_size,free) adr /\
        (
         (cptr_value + 2 + cptr_size = get_endl l adr /\ (brk_value = 0 \/ brk_value = 1)) \/
         (exists  nptr_size, exists nptr_status,
          In_hl l (cptr_value + 2 + cptr_size,nptr_size,nptr_status) adr /\
          ((nptr_status = true /\ brk_value = 1) \/
           (nptr_status = false /\ (brk_value = 1 \/ brk_value = 0))
          )
         )        
        )        
      ) \/ (
        exists cptr_value, exists nptr_value, exists cstts_value,
        (s |b= (var_e cptr) == (nat_e cptr_value)) /\
        (s |b= (var_e nptr) == (nat_e nptr_value)) /\
        (s |b= (var_e cstts) == Allocated) /\
        (s |b= (var_e brk) == (nat_e 1)) /\
           ((cptr_value = get_endl l adr /\
             nptr_value = 0 /\
             cstts_value = Allocated) \/
            (exists cptr_size, exists cptr_status, 
               In_hl l (cptr_value,cptr_size,cptr_status) adr /\
               nptr_value = cptr_value + 2 + cptr_size)
           )))
).

Decompose_hyp.
exists x0.
Resolve_topsy.
inversion_clear H10.
Decompose_hyp.
right.
subst x3.
exists x1; exists x2; exists Allocated.
Resolve_topsy.
Decompose_hyp.
destruct x5.
simpl in H12; subst x3; subst x2.
left.
exists x1; exists x4; exists 1.
Resolve_topsy.
generalize (In_hl_destruct _ _ _ _ _ H9); intros.
Decompose_hyp.
destruct x3.
left.
rewrite H10.
rewrite get_endl_app.
simpl; omega.
destruct p.
right.
exists n; exists b.
rewrite H10.
split; [idtac | destruct b; Resolve_topsy].
apply In_hl_or_app.
right.
simpl.
assert (get_endl x2 adr <> x1 + 2 + x4).
omega.
rewrite (beq_dif_false _ _ H3).
simpl.
rewrite H11.
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
right.
simpl in H12; subst x2 x3.
exists x1; exists (x1 + 2 + x4); exists Allocated.
Resolve_topsy.
right.
exists x4; exists false.
Resolve_topsy.

Step (fun s h => exists l, Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
     (
      exists cptr_value, exists cptr_size, exists brk_value,
        (s |b= var_e cptr == (nat_e cptr_value)) /\
        (s |b= var_e nptr == (nat_e (cptr_value + 2 + cptr_size))) /\
        (s |b= var_e cstts == Free) /\
        (s |b= var_e brk == (nat_e brk_value)) /\
        In_hl l (cptr_value,cptr_size,free) adr /\
        (
         (cptr_value + 2 + cptr_size = get_endl l adr /\ (brk_value = 0 \/ brk_value = 1) /\
          (s |b= (var_e nstts) == Allocated)) \/
         (exists  nptr_size, exists nptr_status,
          In_hl l (cptr_value + 2 + cptr_size,nptr_size,nptr_status) adr /\
          ((nptr_status = true /\ brk_value = 1) \/
           (nptr_status = false /\ (brk_value = 1 \/ brk_value = 0))) /\
           (s |b= (var_e nstts == hlstat_bool2expr nptr_status))         
         )))
).

Decompose_hyp.
inversion_clear H8.
Decompose_hyp.
inversion_clear H13.
Decompose_hyp.
exists Allocated.
unfold status.
apply cell_read.
split.
generalize (hl_getstat' _ _ _ _ H3); intros.
Decompose_sepcon H7 h1 h2.
Compose_sepcon h1 h2.
rewrite H12 in H9.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists x1; exists x2; exists x3.
Resolve_topsy.
left.
Resolve_topsy.
Decompose_hyp.
exists (hlstat_bool2expr x5).
unfold status.
apply cell_read.
split.
generalize (In_hl_destruct _ _ _ _ _ H12); intros.
Decompose_hyp.
rewrite H14 in H3.
generalize (hl_getstatus _ _ _ _ _ _ _ H3); intros.
Decompose_sepcon H7 h1 h2.
Compose_sepcon h1 h2.
rewrite H15 in H16.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists x1; exists x2; exists x3.
Resolve_topsy.
right.
exists x4; exists x5.
destruct x5; Resolve_topsy.
Decompose_hyp.
assert (s |b/= ((var_e cstts == Free) &&& (var_e nptr =/= null)) &&& (var_e brk == nat_e 1)).
Omega_exprb.
Omega_exprb.

Step TT.

Step TT.
intros.
Decompose_hyp.
red.
exists x0.
Resolve_topsy.
left.
inversion_clear H13.
Decompose_hyp.
exists x1; exists x2; exists 0.
Resolve_topsy.
exists x1; exists x2; exists 0.
Resolve_topsy.
Decompose_hyp.
right.
exists x4; exists x5.
Resolve_topsy.
destruct x5.
simpl hlstat_bool2expr in H15.
Omega_exprb.
simpl hlstat_bool2expr in H15.
auto.

Step (fun s h => exists l, Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
     (
      exists cptr_value, exists cptr_size, exists brk_value,
        (s |b= (var_e cptr) == (nat_e cptr_value)) /\
        (s |b= (var_e nptr) == (nat_e (cptr_value + 2 + cptr_size))) /\
        (s |b= (var_e cstts) == Free) /\
        (s |b= (var_e brk) == (nat_e brk_value)) /\
        In_hl l (cptr_value,cptr_size,free) adr /\
        (         
         (exists  nptr_size, exists nptr_status,
          In_hl l (cptr_value + 2 + cptr_size,nptr_size,nptr_status) adr /\
          ((nptr_status = true /\ brk_value = 1)) /\
          (s |b= var_e tmp == nat_e (cptr_value + 2 + cptr_size + 2 + nptr_size))          
         )))
).

Decompose_hyp.
inversion_clear H13.
Decompose_hyp.
assert (s |b= var_e nstts == Free).
Omega_exprb.
assert (s |b= var_e nstts =/= Free).
Omega_exprb.
Omega_exprb.
Decompose_hyp.
destruct x5.
simpl hlstat_bool2expr in H15.

exists (nat_e (x1 + 2 + x2 + 2 + x4)).
unfold next.
apply cell_read.
split.
generalize (In_hl_destruct _ _ _ _ _ H12); intros.
Decompose_hyp.
rewrite H13 in H3.
generalize (hl_getnext _ _ _ _ _ _ _ H3); intros.
Decompose_sepcon H2 h1 h2.
Compose_sepcon h1 h2.
rewrite H16 in H17.
Mapsto.
simpl in H9.
rewrite (Zeq_bool_true _ _ H9).
OmegaZ.
red; auto.
red.
exists x0.
Resolve_topsy.
exists x1; exists x2; exists 1.
inversion_clear H14.
Decompose_hyp.
subst x3.
Resolve_topsy.
exists x4; exists true.
Resolve_topsy.
inversion_clear H2.
inversion H13.
simpl hlstat_bool2expr in H15.
assert (s |b= var_e nstts =/= Free).
Omega_exprb.
Omega_exprb.

Step (fun s h => exists l, Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
     (
      exists cptr_value, exists cptr_size,
        (s |b= var_e cptr == (nat_e cptr_value)) /\
        (s |b= var_e cstts == Free) /\
        (s |b= var_e brk == (nat_e 1)) /\
        In_hl l (cptr_value,cptr_size,free) adr /\
        (s |b= (var_e tmp) == nat_e (cptr_value + 2 + cptr_size))          
     )        
).

Decompose_hyp.
generalize (In_hl_next _ _ _ _ _ _ _ H10 H3); intros.
Decompose_hyp.
subst x5 x3.
rewrite H13 in H2.
unfold free in H2.
generalize (hl_compaction x6 x7 x2 x4 _ s h H2); intros.
unfold next.
rewrite <- H16 in H11.
inversion_clear H11.
Decompose_sepcon H12 h1 h2.
exists x3.
Compose_sepcon h1 h2.
Mapsto.
Intro_sepimp h1' h'.
exists (x6 ++ (x2 + x4 + 2, true) :: x7).
split.
eapply H18 with h1'.
split; auto.
Mapsto.
simpl in H14; rewrite (Zeq_bool_true _ _ H14); OmegaZ.
auto.
split.
rewrite H13 in H5.
generalize (In_hl_app_or _ _ _ _ _ _ H5); intro X; inversion_clear X.
apply In_hl_or_app; left; auto.
simpl in H21.
assert (beq_nat (get_endl x6 adr) x && bool_eq alloc free && beq_nat x2 sizex = false).
apply andb_false_intro1.
apply andb_false_intro2.
auto.
rewrite H22 in H21; clear H22.
assert (beq_nat (get_endl x6 adr + 2 + x2) x && bool_eq alloc true && beq_nat x4 sizex = false).
apply andb_false_intro1.
apply andb_false_intro2.
auto.
rewrite H22 in H21; clear H22.
assert (beq_nat (get_endl x6 adr) x && bool_eq alloc true &&
      beq_nat (x2 + x4 + 2) sizex = false).
apply andb_false_intro1.
apply andb_false_intro2.
auto.
apply In_hl_or_app; right; simpl.
rewrite H22.
cutrewrite (get_endl x6 adr + 2 + (x2 + x4 + 2) = (get_endl x6 adr + 2 + x2 + 2 + x4)); [auto | omega].

Resolve_topsy.
exists x1; exists (x2 + 2 + x4).
Resolve_topsy.
apply In_hl_or_app; right; simpl.
rewrite H16.
cutrewrite (x2 + x4 + 2 = x2 + 2 + x4); [idtac | omega].
repeat rewrite <- beq_nat_refl.
rewrite bool_eq_refl.
simpl; auto.
simpl; simpl in H14; rewrite (Zeq_bool_true _ _ H14).
cutrewrite ((Z_of_nat (x1 + 2 + x2 + 2 + x4)) = (Z_of_nat (x1 + 2 + (x2 + 2 + x4))))%Z; [rewrite Zeq_bool_refl; auto | OmegaZ].

Step TT.
red; intros.
Decompose_hyp.
exists x0.
Resolve_topsy.
left.
exists x1; exists x2; exists 1.
Resolve_topsy.
generalize (In_hl_destruct _ _ _ _ _ H9); intros.
Decompose_hyp.
destruct x4.
left.
rewrite H10; rewrite get_endl_app.
simpl.
omega.
right.
destruct p.
exists n; exists b.
split.
rewrite H10.
eapply In_hl_or_app; right; simpl.
assert (beq_nat (get_endl x3 adr) (x1 + 2 + x2) && bool_eq b free && beq_nat x2 n = false).
apply andb_false_intro1.
apply andb_false_intro1.
apply beq_dif_false.
omega.
rewrite H6; clear H6.
rewrite H12.
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
destruct b; Resolve_topsy.

Step TT.
red; intros.
Decompose_hyp.
inversion_clear H8.
Decompose_hyp.
inversion_clear H13.
Decompose_hyp.
unfold next.
exists (nat_e (x1 + 2 + x2)).
apply cell_read.
split.
generalize (In_hl_destruct _ _ _ _ _ H11); intros.
Decompose_hyp.
rewrite H14 in H3.
generalize (hl_getnext _ _ _ _ _ _ _ H3); intros.
Decompose_sepcon H7 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
Decompose_hyp.
Resolve_topsy.
exists (x1 + 2 + x2).
Resolve_topsy.
Decompose_hyp.
unfold next.
exists (nat_e (x1 + 2 + x2)).
apply cell_read.
split.
generalize (In_hl_destruct _ _ _ _ _ H11); intros.
Decompose_hyp.
rewrite H14 in H3.
generalize (hl_getnext _ _ _ _ _ _ _ H3); intros.
Decompose_sepcon H7 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists (x1 + 2 + x2).
Resolve_topsy.
right; right.
exists x4; exists x5.
Resolve_topsy.
Decompose_hyp.
inversion_clear H12.
Decompose_hyp.
unfold next.
exists (nat_e 0).
apply cell_read.
split.
generalize (hl_getnext' _ _ _ _ H3); intros.
Decompose_sepcon H7 h1 h2.
subst x1 x2 x3.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists 0.
Resolve_topsy.
Decompose_hyp.
exists (nat_e (x1 + 2 + x4)).
apply cell_read.
unfold next.
split.
generalize (In_hl_destruct _ _ _ _ _ H11); intros.
Decompose_hyp.
rewrite H13 in H3.
generalize (hl_getnext _ _ _ _ _ _ _ H3); intros.
Decompose_sepcon H7 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists (x1 + 2 + x4). 
Resolve_topsy.
right.
generalize (In_hl_destruct _ _ _ _ _ H11); intros.
Decompose_hyp.
destruct x7.
left.
rewrite H13; rewrite get_endl_app; simpl; omega.
destruct p.
right.
exists n; exists b.
rewrite H13.
apply In_hl_or_app.
right.
simpl.
assert (get_endl x6 adr <> x1 + 2 + x4).
omega.
rewrite (beq_dif_false _ _ H7); simpl.
cutrewrite (get_endl x6 adr + 2 + x4 = x1 + 2 + x4).
repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
omega.

red; intros.
Decompose_hyp.
exists x0.
Resolve_topsy.
Qed.

(****************************************************************************)

Definition compact_specif:= forall adr size sizex x,
 size > 0 -> adr > 0 ->
 {{ fun s h => exists l, Heap_List l adr s h /\
   In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null) &&& (var_e cptr == nat_e adr)) }}
 compact cptr nptr stts
 {{ fun s h => exists l, Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) }}.

Lemma compact_verif : compact_specif.

unfold compact_specif.
intros.
generalize True; intro H1. (*TODO: removeme *)
unfold compact.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= (var_e hmStart == nat_e adr) &&& ((var_e result) == null)) /\
       exists cur_adr, (s |b= (var_e cptr) == (nat_e cur_adr)) /\
       ( cur_adr = 0 \/
         (cur_adr = get_endl l adr /\
            cur_adr > 0) \/
         (exists cur_size, exists cur_status, In_hl l (cur_adr, cur_size, cur_status) adr /\
            cur_adr > 0)
       )
).

red; intros.
Decompose_hyp.
exists x0.
Resolve_topsy.
exists adr.
split.
Omega_exprb.
destruct x0.
simpl in H5; contradiction.
destruct p.
right; right.
exists n; exists b.
split; auto.
simpl.
repeat rewrite <- beq_nat_refl.
rewrite bool_eq_refl.
simpl; auto.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= ((var_e hmStart) == nat_e adr) &&& (var_e result == null)) /\
       exists cur_adr, (s |b= (var_e cptr) == (nat_e cur_adr)) /\
       ( (cur_adr = get_endl l adr /\
            cur_adr > 0 /\
            s |b= (var_e stts) == Allocated ) \/
         (exists cur_size, exists cur_status, In_hl l (cur_adr, cur_size, cur_status) adr /\
            (s |b= (var_e stts) == (hlstat_bool2expr cur_status)) /\
            cur_adr > 0)
       )
).

Decompose_hyp.
inversion_clear H8.
subst x1.
Omega_exprb.
inversion_clear H2.
Decompose_hyp.
exists (nat_e 0).
unfold status.
apply cell_read.
split.
generalize (hl_getstat' _ _ _ _ H3); intros.
Decompose_sepcon H8 h1 h2.
Compose_sepcon h1 h2.
subst x1.
Mapsto.
red; auto.
red.
exists x0.
split.
eapply Heap_List_inde_store; apply H3.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
exists x1.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
left.
split; auto.
split; auto.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
Decompose_hyp.
generalize (In_hl_destruct _ _ _ _ _ H2); intros.
Decompose_hyp.
unfold status.
exists (hlstat_bool2expr x3).
apply cell_read.
split.
rewrite H10 in H3.
generalize (hl_getstatus _ _ _  _ _ _ _ H3); intros.
Decompose_sepcon H8 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists x1.
Resolve_topsy.
right.
exists x2; exists x3.
Resolve_topsy.
destruct x3; Resolve_topsy.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
       exists cur_adr, (s |b= var_e cptr == nat_e cur_adr) /\
       ( (cur_adr = get_endl l adr /\
            cur_adr > 0 ) \/
         (exists cur_size, exists cur_status, In_hl l (cur_adr, cur_size, cur_status) adr /\
            cur_adr > 0)
       )
).

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= (var_e hmStart == (nat_e adr)) &&& (var_e result == null)) /\
       exists cur_adr, (s |b= (var_e cptr) == (nat_e cur_adr)) /\
       ((exists cur_size, In_hl l (cur_adr, cur_size, free) adr /\
            (s |b= (var_e nptr) == nat_e (cur_adr + 2 + cur_size)) /\
            cur_adr > 0)
       )
).

Decompose_hyp.
inversion_clear H8.
Decompose_hyp.
assert (s |b= Allocated == Free).
Omega_exprb.
assert (s |b= Allocated =/= Free).
Omega_exprb.
Omega_exprb.
Decompose_hyp.
destruct x3.
simpl hlstat_bool2expr in H10.
exists (nat_e (x1 + 2 + x2)).
unfold next.
apply cell_read.
split.
generalize (In_hl_destruct _ _ _ _ _ H8); intros.
Decompose_hyp.
rewrite H9 in H3.
generalize (hl_getnext _ _ _ _ _ _ _ H3); intros.
Decompose_sepcon H2 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists x1.
Resolve_topsy.
exists x2.
Resolve_topsy.
simpl hlstat_bool2expr in H10.
assert (s |b= Allocated == Free).
Omega_exprb.
assert (s |b= Allocated =/= Free).
Omega_exprb.
Omega_exprb.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
       exists cur_adr, (s |b= (var_e cptr) == (nat_e cur_adr)) /\
       ((exists cur_size, In_hl l (cur_adr, cur_size, free) adr /\
            (s |b= (var_e nptr) == (nat_e (cur_adr + 2 + cur_size))) /\
            cur_adr > 0 /\ (
            (exists next_size, 
                exists next_status, 
                   In_hl l ((cur_adr + 2 + cur_size), next_size, next_status) adr /\
                   (s |b= (var_e stts) == (hlstat_bool2expr next_status))) \/
                   
                   ((cur_adr + 2 + cur_size) = get_endl l adr /\
                     (s |b= (var_e stts) == Allocated ))
            )
       )
)).

Decompose_hyp.
generalize (In_hl_destruct _ _ _ _ _ H7); intros.
Decompose_hyp.
destruct x4.
exists Allocated.
unfold status.
apply cell_read.
split.
rewrite H8 in H2.
generalize (hl_getstat' _ _ _ _ H2); intros.
Decompose_sepcon H3 h1 h2.
Compose_sepcon h1 h2.
rewrite get_endl_app in H12.
subst x1.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists x1.
Resolve_topsy.
exists x2.
Resolve_topsy.
right.
Resolve_topsy.
rewrite H8; rewrite <- H11; rewrite get_endl_app; simpl; omega.
destruct p.
exists (hlstat_bool2expr b).
unfold status.
apply cell_read.
split.
rewrite H8 in H2.
assert (x3 ++ (x2,free)::(n,b)::x4 = (x3 ++ (x2,free)::nil) ++ (n,b)::x4).
rewrite app_ass.
auto.
rewrite H3 in H2.
generalize (hl_getstatus _ _ _ _ _ _ _ H2); intros.
Decompose_sepcon H12 h1 h2.
Compose_sepcon h1 h2.
rewrite get_endl_app in H13.
simpl get_endl in H13.
subst x1.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists x1.
Resolve_topsy.
exists x2.
Resolve_topsy.
left.
exists n; exists b.
split.
rewrite H8.
apply In_hl_or_app.
right.
simpl.
assert (get_endl x3 adr <> x1 + 2 + x2).
omega.
rewrite (beq_dif_false _ _ H3).
simpl.
subst x1.
repeat rewrite <- beq_nat_refl.
rewrite bool_eq_refl.
simpl; auto.
destruct b; Resolve_topsy.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
       exists cur_adr, (s |b= (var_e cptr) == nat_e cur_adr) /\
       ((exists cur_size, In_hl l (cur_adr, cur_size, free) adr /\
            (s |b= (var_e nptr) == (nat_e (cur_adr + 2 + cur_size))) /\
            cur_adr > 0 /\ (
            (exists next_size, 
                exists next_status, 
                   In_hl l ((cur_adr + 2 + cur_size), next_size, next_status) adr /\
                   (s |b= (var_e stts) == (hlstat_bool2expr next_status))) \/
                   
                   ((cur_adr + 2 + cur_size) = get_endl l adr /\
                     (s |b= var_e stts == Allocated ))
            )))
).

red; intros.
trivial.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
       exists cur_adr, (s |b= var_e cptr == nat_e cur_adr) /\
       ((exists cur_size,  In_hl l (cur_adr, cur_size, free) adr /\
            (s |b= (var_e nptr) == (nat_e (cur_adr + 2 + cur_size))) /\
            cur_adr > 0 /\ (
            (exists next_size, 
                   In_hl l ((cur_adr + 2 + cur_size), next_size, free) adr /\
                   (s |b= (var_e stts) == (nat_e (cur_adr + 2 + cur_size + 2 + next_size))))
            )))
).

Decompose_hyp.
inversion_clear H12.
Decompose_hyp.
destruct x4.
generalize (In_hl_destruct _ _ _ _ _ H11); intros.
Decompose_hyp.

exists (nat_e (x1 + 2 + x2 + 2 +x3)).
unfold next.
eapply cell_read.
split.
rewrite H13 in H3.
generalize (hl_getnext _ _ _ _ _ _ _ H3); intros.
Decompose_sepcon H2 h1 h2 .
Compose_sepcon h1 h2.
rewrite <- H14 in H10.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists x1.
Resolve_topsy.
exists x2.
Resolve_topsy.
exists x3.
Resolve_topsy.

simpl hlstat_bool2expr in H12.

assert (s |b= Allocated == Free).
Omega_exprb.
assert (s |b= Allocated =/= Free).
Omega_exprb.
Omega_exprb.
inversion_clear H2.

assert (s |b= Allocated == Free).
Omega_exprb.
assert (s |b= Allocated =/= Free).
Omega_exprb.
Omega_exprb.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
       exists cur_adr, (s |b= (var_e cptr) == (nat_e cur_adr)) /\
       (exists cur_size, 
            In_hl l (cur_adr, cur_size, free) adr /\            
            cur_adr > 0 /\
            (s |b= (var_e stts) == nat_e (cur_adr + 2 + cur_size))
       )
).

Decompose_hyp .
generalize (In_hl_next _ _ _ _ _ _ _ H7 H10); intros.
inversion_clear H3 as [x4].
inversion_clear H12 as [x7].
unfold next.
inversion_clear H3.
rewrite H12 in H2.
generalize (hl_compaction _ _ _ _ _ _ _ H2); intros.
inversion_clear H3.
Decompose_hyp.
exists x5.
Compose_sepcon H3 H14.
Mapsto.
Intro_sepimp h1' h'.
exists (x4 ++ (x2 + x3 + 2, true) :: x7).
split.
eapply H19.
split.
apply H18.
rewrite <- H13.
cutrewrite (x1 + x2 + x3 + 4 = x1 + 2 + x2 + 2 + x3).
Mapsto.
omega.
auto.
split.
rewrite H12 in H5.
generalize (In_hl_app_or _ _ _ _ _ _ H5); intro X; inversion_clear X.
apply In_hl_or_app.
left; auto.
simpl in H22.
assert (beq_nat (get_endl x4 adr) x && bool_eq alloc free && beq_nat x2 sizex = false).
apply andb_false_intro1.
apply andb_false_intro2.
auto.
rewrite H23 in H22.
assert (beq_nat (get_endl x4 adr + 2 + x2) x && bool_eq alloc free && beq_nat x3 sizex = false).
apply andb_false_intro1.
apply andb_false_intro2.
auto.
rewrite H24 in H22.
apply In_hl_or_app.
right.
simpl.
assert (beq_nat (get_endl x4 adr) x && bool_eq alloc true && beq_nat (x2 + x3 + 2) sizex = false).
apply andb_false_intro1.
apply andb_false_intro2.
auto.
rewrite H25.
cutrewrite ((get_endl x4 adr + 2 + (x2 + x3 + 2)) = (get_endl x4 adr + 2 + x2 + 2 + x3)); [auto | omega].
Resolve_topsy.
exists x1.
Resolve_topsy.

exists (x2+ x3 + 2).
split.
apply In_hl_or_app.
right.
simpl.
subst x1.
repeat rewrite <- beq_nat_refl.
rewrite bool_eq_refl.
simpl; auto.
split; auto.
cutrewrite ((x1 + 2 + (x2 + x3 + 2)) = (x1 + 2 + x2 + 2 + x3)); [auto | omega].

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
       exists cur_adr, (s |b= var_e cptr == nat_e cur_adr) /\
       (exists cur_size, 
            In_hl l (cur_adr, cur_size, free) adr /\            
            cur_adr > 0 /\
            (s |b= var_e nptr == nat_e (cur_adr + 2 + cur_size))
       )
).

Decompose_hyp.
red.
exists x0.
Resolve_topsy.
exists x1.
Resolve_topsy.
exists x2.
Resolve_topsy.

Step TT.

red; intros.
Decompose_hyp.
generalize (In_hl_destruct _ _ _ _ _ H7); intros.
Decompose_hyp.
destruct x4.
exists Allocated.
eapply cell_read.
unfold status.
split.
generalize (hl_getstat' _ _ _ _ H2); intros.
Decompose_sepcon H3 h1 h2.
rewrite H8 in H12.
rewrite get_endl_app in H12.
simpl get_endl in H12.
rewrite H11 in H12.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists x1.
Resolve_topsy.
exists x2.
Resolve_topsy.
right.
Resolve_topsy.
rewrite H8.
rewrite get_endl_app.
simpl; omega.
destruct p.
exists (hlstat_bool2expr b).
unfold status.
eapply cell_read.
split.
assert (x0 = (x3 ++(x2,free)::nil) ++ (n,b)::x4).
rewrite app_ass.
auto.
rewrite H3 in H2.
generalize (hl_getstatus _ _ _ _ _ _ _ H2); intros.
Decompose_sepcon H12 h1 h2.
Compose_sepcon h1 h2.
subst x1.
rewrite get_endl_app in H13.
simpl get_endl in H13.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists x1.
Resolve_topsy.
exists x2.
Resolve_topsy.
left.
exists n; exists b.
split.
rewrite H8.
apply In_hl_or_app.
right.
simpl.
assert (get_endl x3 adr <> x1 + 2 + x2).
omega.
rewrite (beq_dif_false _ _ H3).
simpl.
subst x1.
repeat rewrite <- beq_nat_refl.
rewrite bool_eq_refl.
simpl; auto.
destruct b; Resolve_topsy.

red; intros.
Decompose_hyp.
exists x0.
Resolve_topsy.
exists x1.
Resolve_topsy.
right.
exists x2; exists free.
Resolve_topsy.

Step TT.
red; intros.
Decompose_hyp.
exists x0.
Resolve_topsy.
exists x1.
Resolve_topsy.
inversion_clear H8.
Decompose_hyp.
left.
Resolve_topsy.
Decompose_hyp.
right.
exists x2; exists x3.
Resolve_topsy.

Step TT.
red; intros.
Decompose_hyp.
unfold next.
inversion_clear H7.
Decompose_hyp.
exists (nat_e 0).
apply cell_read.
split.
generalize (hl_getnext' _ _ _ _ H2); intros.
Decompose_sepcon H3 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists 0.
Resolve_topsy.
Decompose_hyp.
generalize (In_hl_destruct _ _ _ _ _ H7); intros.
exists (nat_e (x1 + 2 + x2)).
Decompose_hyp.
apply cell_read.
split.
rewrite H9 in H2.
generalize (hl_getnext _ _ _ _ _ _ _ H2); intros.
Decompose_sepcon H3 h1 h2.
Compose_sepcon h1 h2.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists (x1 + 2 + x2).
Resolve_topsy.
destruct x5.
right; left.
rewrite H9; rewrite get_endl_app; simpl.
split; omega.
right; right.
destruct p.
exists n; exists b.
split; try omega.
rewrite H9.
apply In_hl_or_app.
right.
simpl.
assert (get_endl x4 adr <> x1 + 2 +x2); try omega.
rewrite (beq_dif_false _ _ H3); simpl.
subst x1; repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.

red; intros.
Decompose_hyp.
exists x0.
Resolve_topsy.
Qed.

(****************************************************************************)

Definition split_specif := forall adr size sizex x, 
  size > 0 -> adr > 0 ->
  {{ fun s h =>  exists l, Heap_List l adr s h /\ 
     In_hl l (x,sizex,alloc) adr /\ 
     (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\    
     (exists y, exists size'', size'' >= size /\ 
       In_hl l (y,size'',free) adr /\ 
       (s |b= var_e entry == nat_e y) /\ 
       y > 0 /\ y <> x) }}
  split entry size cptr sz
  {{ fun s h => exists l, In_hl l (x,sizex,alloc) adr /\ 
     (exists y, y > 0 /\ (s |b= var_e entry == nat_e y) /\
       (exists size'', size'' >= size /\      
         (Heap_List l adr ** Array (y+2) size'') s h /\ 
         In_hl l (y,size'',alloc) adr /\ y <> x)) }}.

Lemma split_verif : split_specif.

unfold split_specif.
intros.
unfold split.
unfold ENTRYSIZE.
unfold LEFTOVER.

Step (fun s h =>  exists l,
    Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\    
    (exists y, exists size'', size'' >= size /\ 
     In_hl l (y,size'',free) adr /\ 
     (s |b= (var_e entry) == nat_e y) /\ 
     y > 0 /\
     y <> x /\
     (s |b= var_e sz == nat_e size''))
).

Step (fun s h =>  exists l,
    Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\    
    (exists y, exists size'', size'' >= size /\ 
     In_hl l (y,size'',free) adr /\ 
     (s |b= (var_e entry == nat_e y)) /\ 
     y > 0 /\
     y <> x /\
     (s |b= var_e sz == (nat_e (y + 2 + size''))))
).

Decompose_hyp.
exists (nat_e (x1 + 2 + x2)).
apply cell_read.
unfold next.
split.
generalize (In_hl_destruct _ _ _ _ _ H7); intros.
Decompose_hyp.
rewrite H9 in H1.
generalize (hl_getnext _ _ _ _ _ _ _ H1); intros.
Decompose_sepcon H5 h1 h2.
Compose_sepcon h1 h2.
subst x1.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists x1; exists x2.
Resolve_topsy.

Step (fun s h =>  exists l,
    Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\    
    (exists y, exists size'', size'' >= size /\ 
     In_hl l (y,size'',free) adr /\ 
     (s |b= (var_e entry == nat_e y)) /\ 
     y > 0 /\
     y <> x /\
     (s |b= var_e sz == nat_e size''))
).

Decompose_hyp.
red.
exists x0.
Resolve_topsy.
exists x1; exists x2.
Resolve_topsy.
rewrite <- expr_b_store_update_rewrite.
simpl expr_b_rewrite.
simpl; simpl in H6; simpl in H11.
rewrite (Zeq_bool_true _ _ H11).
rewrite (Zeq_bool_true _ _ H6).
cutrewrite (Z_of_nat (x1 + 2 + x2) - Z_of_nat x1 - 2 = Z_of_nat x2)%Z.
apply Zeq_bool_refl.
OmegaZ.

Step TT.

Step TT.
intros.
Decompose_hyp.
assert (s |b/= nat_e 0 >> var_e sz).
Omega_exprb.
Omega_exprb.

Step TT.
red; intros.
intuition.

Step (fun s h =>  exists l,
    Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\    
    (exists y, exists size'', size'' >= size /\ 
     In_hl l (y,size'',free) adr /\ 
     (s |b= (var_e entry) == nat_e y) /\ 
     y > 0 /\
     y <> x )
).

Step (fun s h =>  exists l,
    Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\    
    (exists y, exists size'', size'' >= size /\ 
     In_hl l (y,size'',free) adr /\ 
     (s |b= (var_e entry == nat_e y)) /\ 
     y > 0 /\
     y <> x /\
     (s |b= (var_e sz == nat_e size'')) /\
     size'' >= size + LEFTOVER + 2 /\
     (s |b= (var_e cptr == nat_e (y + 2 + size))))
).

unfold LEFTOVER.
Decompose_hyp.
red.
exists x0.
Resolve_topsy.
exists x1; exists x2.
Resolve_topsy.
assert (s |b= nat_e x2 >>= (nat_e size +e nat_e LEFTOVER +e nat_e 2)).
Resolve_topsy.
Omega_exprb.

Step (fun s h =>  exists l,
    Heap_List l adr s h /\ 
    In_hl l (x,sizex,alloc) adr /\ 
    (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\    
    (exists y, exists size'', size'' >= size /\ 
     In_hl l (y,size'',free) adr /\ 
     (s |b= (var_e entry) == nat_e y) /\ 
     y > 0 /\
     y <> x /\
     (s |b= (var_e sz == nat_e (y + 2 + size''))) /\
     size'' >= size + LEFTOVER + 2 /\
     (s |b= (var_e cptr) == (nat_e (y + 2 + size))))
).

Decompose_hyp.
exists (nat_e (x1 + 2 + x2)).
apply cell_read.
unfold next.
split.
generalize (In_hl_destruct _ _ _ _ _ H7); intros.
Decompose_hyp.
rewrite H12 in H1.
generalize (hl_getnext _ _ _ _ _ _ _ H1); intros.
Decompose_sepcon H5 h1 h2.
Compose_sepcon h1 h2.
subst x1.
Mapsto.
red; auto.
red.
exists x0.
Resolve_topsy.
exists x1; exists x2; Resolve_topsy.

Step (fun s h => exists e'',
     ((cptr -.> status) |-> e'' **
      ((cptr -.> status) |-> Free -*
       (fun s0 h0 => exists e''0,
          ((entry -.> next) |-> e''0 **
           ((entry -.> next) |-> var_e cptr -*
            (fun s1 h1 => exists l,
            Heap_List l adr s h1 /\
            In_hl l (x, sizex, alloc) adr /\
            (s1 |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
            (exists y,
            (exists size'',
            size'' >= size /\
            In_hl l (y, size'', free) adr /\
            (s1 |b= var_e entry == nat_e y) /\
            y > 0 /\ y <> x))
))) s0 h0
))) s h) .

Decompose_hyp.
assert (x2 = size + 2 + (x2 - 2 - size)).
omega.
rewrite H5 in H7.
generalize (In_hl_destruct _ _ _ _ _ H7); intros.
Decompose_hyp.
rewrite H14 in H1.
generalize (hl_splitting _ _ _ _ _ _ _ H1); intros.
inversion_clear H12.
exists x5.
Decompose_sepcon H16 h1 h2.
unfold next.
Compose_sepcon h1 h2.
rewrite H15 in H16.
Mapsto.
simpl in H13.
rewrite (Zeq_bool_true _ _ H13).
OmegaZ.
Intro_sepimp h1' h'.
red in H19.
assert (
  h2 # h1' /\
  (nat_e (get_endl x3 adr + size + 3) |-> nat_e (get_endl x3 adr + size + (x2 - 2 - size) + 4)) s h1'
).
split; (Mapsto || auto).
simpl in H13; rewrite (Zeq_bool_true _ _ H13).
OmegaZ.
simpl in H10; rewrite (Zeq_bool_true _ _ H10).
OmegaZ.
generalize (H19 _ H22 _ H21); clear H19 H22; intro X; inversion_clear X.
exists x6.
Decompose_sepcon H19 h'1 h'2.
unfold status.
Compose_sepcon h'1 h'2.
Mapsto.
simpl in H13; rewrite (Zeq_bool_true _ _ H13).
OmegaZ.
Intro_sepimp h'1' h''.
red in H25.
assert (
h'2 # h'1' /\ (nat_e (get_endl x3 adr + size + 2) |-> Free) s h'1'
).
split; auto.
Mapsto.
simpl in H13; rewrite (Zeq_bool_true _ _ H13).
OmegaZ.
generalize (H25 _ H28 _ H27); clear H25 H28; intro X; inversion_clear X.
exists x7.
Decompose_sepcon H25 h''1 h''2.
Compose_sepcon h''1 h''2.
Mapsto.
Intro_sepimp h''1' h'''.
red in H31.
assert (
  h''2 # h''1' /\
  (nat_e (get_endl x3 adr + 1) |-> nat_e (get_endl x3 adr + size + 2)) s h''1'
).
split; auto.
Mapsto.
simpl in H13; rewrite (Zeq_bool_true _ _ H13).
OmegaZ.
generalize (H31 _ H34 _ H33); clear H31 H34; intros.
exists  (x3 ++ (size, true) :: (x2 - 2 - size, true) :: x4) .
split; auto.
Resolve_topsy.
rewrite H14 in H4.
generalize (In_hl_app_or _ _ _ _ _ _ H4); intro X; inversion_clear X.
apply In_hl_or_app.
left; auto.
simpl in H34.
assert (beq_nat (get_endl x3 adr) x && bool_eq alloc free && beq_nat (size + 2 + (x2 - 2 - size)) sizex = false).
apply andb_false_intro1.
apply andb_false_intro2.
simpl; auto.
rewrite H35 in H34; clear H35.
apply In_hl_or_app.
right; simpl.
assert (beq_nat (get_endl x3 adr) x && bool_eq alloc true && beq_nat size sizex = false).
apply andb_false_intro1.
apply andb_false_intro2.
simpl; auto.
rewrite H35; clear H35.
assert (beq_nat (get_endl x3 adr + 2 + size) x && bool_eq alloc true && beq_nat (x2 - 2 - size) sizex = false).
apply andb_false_intro1.
apply andb_false_intro2.
simpl; auto.
rewrite H35; clear H35.
cutrewrite ((get_endl x3 adr + 2 + size + 2 + (x2 - 2 - size)) = (get_endl x3 adr + 2 + (size + 2 + (x2 - 2 - size)))); [auto | omega].
exists x1; exists size.
Resolve_topsy.
apply In_hl_or_app.
right; simpl.
subst x1; unfold free.
repeat rewrite <- beq_nat_refl.
rewrite bool_eq_refl.
simpl; auto.

Step (fun s0 h0 => exists e'',
      ((entry -.> next) |-> e'' **
       ((entry -.> next) |-> var_e cptr -*
        (fun s h => exists l,
           Heap_List l adr s h /\
           In_hl l (x, sizex, alloc) adr /\
           (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
           (exists y,
              (exists size'', size'' >= size /\
                 In_hl l (y, size'', free) adr /\
                 (s |b= var_e entry == nat_e y) /\
                 y > 0 /\ y <> x))))) s0 h0).
trivial.

Step TT.
red; intros.
trivial.

Step TT.
red; intros.
Decompose_hyp.
exists x0.
Resolve_topsy.
exists x1; exists x2; Resolve_topsy.

Step TT.
red; intros.
Decompose_hyp.
generalize (In_hl_destruct _ _ _ _ _ H7); intros.
Decompose_hyp.
rewrite H9 in H1.
generalize (hl_free2alloc _ _ _ _ _ _ H1); intros.
Decompose_hyp.
exists x5.
unfold status.
Compose_sepcon H5 H12.
Mapsto.
Intro_sepimp h1 h'.
red in H17.
assert(
  H12 # h1 /\ (nat_e (get_endl x3 adr) |-> Allocated) s h1
).
split; (Mapsto || auto).
generalize (H17 _ H20 _ H19); clear H20 H17; intros.
exists (x3 ++ (x2,false)::x4).
Resolve_topsy.
rewrite H9 in H4.
generalize (In_hl_app_or _ _ _ _ _ _ H4); intro X; inversion_clear X.
apply In_hl_or_app.
left; auto.
simpl in H20.
assert(
beq_nat (get_endl x3 adr) x && bool_eq alloc free && beq_nat x2 sizex = false
).
apply andb_false_intro1.
apply andb_false_intro2.
simpl; auto.
rewrite H21 in H20.
apply In_hl_or_app.
right; simpl.
assert (get_endl x3 adr <> x).
omega.
rewrite (beq_dif_false _ _ H22); simpl; auto.
exists x1.
Resolve_topsy.
simpl in H6.
exists x2.
Resolve_topsy.
Decompose_sepcon H17 h11 h12.
Compose_sepcon h11 h12.
auto.
Array_equiv.
apply In_hl_or_app.
right; simpl.
subst x1; repeat rewrite <- beq_nat_refl; rewrite bool_eq_refl; simpl; auto.
Qed.

(****************************************************************************)

Definition hmAlloc_specif := forall adr x sizex size, 
  adr > 0 -> size > 0 ->
  {{ fun s h => exists l, Heap_List l adr s h /\
     In_hl l (x,sizex,alloc) adr /\
     (s |b= var_e hmStart == nat_e adr) }}
  hmAlloc result size entry cptr fnd stts nptr sz
  {{ fun s h => 
     (exists l, exists y, y > 0 /\ (s |b= var_e result == nat_e (y+2)) /\
      exists size'', size'' >= size /\
      (Heap_List l adr ** Array (y + 2) size'') s h /\ 
      In_hl l (x,sizex,alloc) adr /\ In_hl l (y,size'',alloc) adr /\ 
      x <> y)
     \/
     (exists l, (s |b= var_e result == nat_e 0) /\ 
       Heap_List l adr s h /\ In_hl l (x,sizex,alloc) adr) }}.

Lemma hmAlloc_verif: hmAlloc_specif.
unfold hmAlloc_specif.
intros.
unfold hmAlloc.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x,sizex,alloc) adr /\
       (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null))
).

Decompose_hyp.
red.
exists x0.
Resolve_topsy.

Step (fun s h => exists l,
       Heap_List l adr s h /\
       In_hl l (x,sizex,alloc) adr /\
       (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
       ((exists y,
           (exists size'',
              size'' >= size /\
              In_hl l (y, size'', free) adr /\
              (s |b= (var_e entry == nat_e y)) /\
              y > 0)) \/ (s |b= var_e entry == null))
).

generalize (findFree_verif adr x sizex size H0 H); intros.

Step TT.
red; intros.
trivial.
red; intros.
clear H1.
Decompose_hyp.
exists x0.
Resolve_topsy.
inversion_clear H6; Decompose_hyp.
left; exists x1; exists x2; Resolve_topsy.
Eval_b_hyp H8.
OmegaZ.
right.
auto.

Step (fun s h => exists l, Heap_List l adr s h /\
       In_hl l (x,sizex,alloc) adr /\
       (s |b= (var_e hmStart == nat_e adr) &&& (var_e result == null)) /\
       ((exists y,
           (exists size'',
              size'' >= size /\
              In_hl l (y, size'', free) adr /\
              (s |b= (var_e entry == nat_e y)) /\
              y > 0)) \/ (s |b= var_e entry == null))
).

Step (fun s h => exists l, Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= var_e hmStart == nat_e adr) /\
       (s |b= var_e result == null) /\
       (s |b= var_e entry == null) /\
       (s |b= var_e cptr == var_e hmStart)
).

Decompose_hyp.
inversion_clear H7; Decompose_hyp.
assert (s |b= var_e entry =/= null).
Omega_exprb.
Omega_exprb.
red.
exists x0.
Resolve_topsy.

Step (fun s h => exists l, Heap_List l adr s h /\
       In_hl l (x, sizex, alloc) adr /\
       (s |b= var_e hmStart == nat_e adr &&& (var_e result == null))
).

generalize (compact_verif adr size sizex x H0 H); intros.
Step TT.
clear H1;
red; intros.
Decompose_hyp.
exists x0.
Resolve_topsy.
red; intros.
Decompose_hyp.
exists x0.
Resolve_topsy.

generalize (findFree_verif adr x sizex size H0 H); intros.

Step TT.
red; intros.
clear H1.
trivial.
red; intros.
Decompose_hyp.
exists x0.
Resolve_topsy.
inversion_clear H7; Decompose_hyp.
left; exists x1; exists x2; Resolve_topsy.
Eval_b_hyp H9.
OmegaZ.
right.
auto.

Step TT.
red; intros.
tauto.

Step TT.

Step TT.
intros.
red.
Decompose_hyp.
inversion_clear H7; Decompose_hyp.
assert (s |b= var_e entry =/= null).
Omega_exprb.
Omega_exprb.
right.
exists x0.
Resolve_topsy.

Step (fun s h => exists l,
        exists y,
           y > 0 /\
           (s |b= var_e entry == nat_e y) /\
           (exists size'',
              size'' >= size /\
              (Heap_List l adr ** Array (y + 2) size'') s h /\
              In_hl l (x, sizex, alloc) adr /\
              In_hl l (y, size'', alloc) adr /\ x <> y)
).

generalize (split_verif adr size sizex x H0 H); intros.

Step TT.
clear H1.
red; intros.
Decompose_hyp.
inversion_clear H7; Decompose_hyp.
exists x0.
Resolve_topsy.
exists x1; exists x2.
Resolve_topsy.
apply (In_hl_dif _ _ _ _ _ _ H5 H8).
Omega_exprb.
clear H1.
red; intros.
Decompose_hyp.
exists x0.
exists x1.
Resolve_topsy.
exists x2.
Resolve_topsy.
Compose_sepcon H2 H7; auto.

Step TT.
intros; red.
Decompose_hyp.
left.
exists x0.
exists x1.
Resolve_topsy.
exists x2.
Resolve_topsy.
Compose_sepcon H1 H6.
Resolve_topsy.
Array_equiv.
Qed.


