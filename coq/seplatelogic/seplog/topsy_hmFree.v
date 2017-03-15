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

(*
113 Error hmFree(Address address)
114 {
115     HmEntry  entry, addressEntry;
116 
117     /* check first if pointer is inside the heap */
118     if (((unsigned long)start > (unsigned long)address) || 
119          ((unsigned long)address >= ((unsigned long)end - LEFTOVER))) {
120         WARNING("hmFree got non-heap pointer");
121         return HM_FREEFAILED;
122     }
123 
124     /*** here we enter a critical section */
125     lock(hmLock);
126 
127     entry = start;
128     addressEntry = (HmEntry)((unsigned long)address - sizeof(HmEntryDesc));
129     while (entry != NULL) {
130         if (entry == addressEntry) break;
131         entry = entry->next;
132     }
133     if (entry == NULL) {
134         unlock( hmLock);
135         return HM_FREEFAILED;
136     }
137     entry->status = HM_FREED;
138 
139     unlock( hmLock);
140     return HM_FREEOK;
141 }
*)
Definition hmFree (address: loc) (entry addressEntry tmp result: var.v) :=
entry <- var_e hmStart;
addressEntry <- (nat_e address -e int_e 2%Z);
while ((var_e entry =/= null) &&& (var_e entry =/= var_e addressEntry)) (
   tmp <-* (entry -.> next);
   entry <- var_e tmp
);
ifte (var_e entry =/= null) thendo (
  tmp <-* (entry -.> next);
  ifte (var_e tmp =/= null) thendo (
    (entry -.> status) *<- Free;
    result <- HM_FREEOK) 
  elsedo 
    (result <- HM_FREEFAILED)
) elsedo (
   result <- HM_FREEFAILED
).

Definition hmFree_specif := forall p x sizex y sizey statusy, p > 0 -> 
  {{ fun s h => exists l, (Heap_List l p ** Array (x+2) sizex) s h /\ 
     In_hl l (x,sizex, alloc) p /\ In_hl l (y,sizey, statusy) p /\ 
     x <> y /\
     s |b= var_e hmStart == nat_e p }}
  hmFree (x+2) entry cptr nptr result
  {{ fun s h => exists l, Heap_List l p s h /\ 
     In_hl l (x,sizex,free) p /\ In_hl l (y,sizey,statusy) p /\
     s |b= var_e result == HM_FREEOK }}.

Lemma hmFree_verif : hmFree_specif.
unfold hmFree_specif.
unfold hmFree.
intros.
generalize True; intro H0. (*TODO: removeme*)

Step  (fun s h => exists l, (Heap_List l p ** Array (x+2) sizex) s h /\ 
      In_hl l (x,sizex, alloc) p /\ 
      In_hl l (y,sizey, statusy) p /\ 
      x <> y /\
      (s |b= (var_e hmStart) == (nat_e p)) /\
      s |b= (var_e entry) == nat_e p
).
red.
Decompose_hyp.
exists x0.
split.
Compose_sepcon H2 H1.
Heap_List_equiv.
Array_equiv.
split; auto.
split; auto.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.

Step  (fun s h => exists l, (Heap_List l p ** Array (x+2) sizex) s h /\ 
      In_hl l (x,sizex, alloc) p /\ 
      In_hl l (y,sizey, statusy) p /\ 
      x <> y /\
      (s |b= (var_e hmStart) == (nat_e p)) /\
      (s |b= (var_e entry) == (nat_e p)) /\
      (s |b= (var_e cptr) == (nat_e x))
).
red.
Decompose_hyp.
exists x0.
split.
Compose_sepcon H2 H1.
Heap_List_equiv.
Array_equiv.
split; auto.
split; auto.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.

Step (fun s h =>
     exists l,
       (Heap_List l p ** Array (x + 2) sizex) s h /\
       In_hl l (x, sizex, alloc) p /\
       In_hl l (y, sizey, statusy) p /\
       x <> y /\
       (s |b= var_e hmStart == nat_e p) /\
       (s |b= var_e cptr == nat_e x) /\
       (exists l1, exists size, exists stat, exists l2,
          l = l1 ++ (size,stat)::l2 /\
          (s |b= var_e entry == nat_e (get_endl l1 p)) /\
          ~ (In_hl l1 (x, sizex, alloc) p)
       )
).

Decompose_hyp.
exists x0.
split.
Compose_sepcon H2 H1; auto.  
split; auto.
split; auto.
split; auto.
split; auto.
split; auto.
destruct x0.
simpl in H4.
contradiction.
destruct p0.
exists (@nil (nat*bool)) ; exists n; exists b; exists x0.
split; auto.

Step (fun s h =>
     exists l,
       (Heap_List l p ** Array (x + 2) sizex) s h /\
       In_hl l (x, sizex, alloc) p /\
       In_hl l (y, sizey, statusy) p /\
       x <> y /\
       (s |b= var_e hmStart == nat_e p) /\
       (s |b= var_e cptr == nat_e x) /\
       (exists l1, exists size, exists stat, exists l2,
          l = l1 ++ (size,stat)::l2 /\
          (s |b= var_e entry == nat_e (get_endl l1 p)) /\
          (s |b= var_e nptr == nat_e (get_endl l1 p + size + 2)) /\
          (s |b= (var_e entry =/= null) &&& (var_e entry =/= var_e cptr)) /\
          ~ (In_hl l1 (x, sizex, alloc) p)
       )
).

Decompose_hyp.
exists (nat_e (get_endl x1 p + x2 + 2)).
apply cell_read.
split.
rewrite H13 in H11.
generalize (hl_getnext _ _ _ _ _ _ _ H11); intros. 
Decompose_sepcon H10 h1 h2.
Compose_sepcon h1 (h2 +++ H2).
unfold next.
Mapsto.
red; auto.
red.
exists x0.
split.
Compose_sepcon H1 H2.
eapply Heap_List_inde_store; apply H11.
Array_equiv.
split; auto.
split; auto.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
exists x1; exists x2; exists x3; exists x4.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
auto.

Step TT.
intros.
Decompose_hyp.
red.
exists x0.
split.
Compose_sepcon H2 H1.
eapply Heap_List_inde_store; apply H10.
Array_equiv.
split; auto.
split; auto.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
destruct x4.

rewrite H12 in H4.
generalize (In_hl_app_or _ _ _ _ _ _ H4); intro X; inversion_clear X.
contradiction.
simpl in H9.
assert (beq_nat (get_endl x1 p) x && bool_eq alloc x3 && beq_nat x2 sizex = false).
apply andb_false_intro1.
apply andb_false_intro1.
apply beq_dif_false.
assert (s |b= nat_e (get_endl x1 p) =/= nat_e x).
Omega_exprb.
Omega_exprb.
rewrite H17 in H9.
contradiction.
destruct p0.
exists (x1 ++ (x2,x3)::nil); exists n; exists b; exists x4.
split.
rewrite <- ass_app.
auto.
split.
rewrite <- expr_b_store_update_rewrite.
rewrite get_endl_app.
simpl get_endl.
simpl expr_b_rewrite.
simpl.
simpl in H14.
cutrewrite (Z_of_nat (get_endl x1 p + 2 + x2) = Z_of_nat (get_endl x1 p + x2 + 2)).
auto.
auto with *.
red; intros.
generalize (In_hl_app_or _ _ _ _ _ _ H9); intros.
inversion_clear H17.
tauto.
simpl in H19.
assert (beq_nat (get_endl x1 p) x && bool_eq alloc x3 && beq_nat x2 sizex = false).
apply andb_false_intro1.
apply andb_false_intro1.
apply beq_dif_false.
assert (s |b= nat_e (get_endl x1 p) =/= nat_e x).
Omega_exprb.
Omega_exprb.
rewrite H17 in H19; tauto.

Step TT.

Step (fun s h =>
     ((exists l,
         (Heap_List l p ** Array (x + 2) sizex) s h /\
         In_hl l (x, sizex, alloc) p /\
         In_hl l (y, sizey, statusy) p /\
         x <> y /\
         (s |b= var_e hmStart == nat_e p) /\
         (s |b= var_e cptr == nat_e x) /\
         (exists l1,
            (exists size,
               (exists stat,
                  (exists l2,
                     l = l1 ++ (size, stat) :: l2 /\
                     (s |b= var_e entry == nat_e (get_endl l1 p)) /\
                     ~ In_hl l1 (x, sizex, alloc) p) /\
                     (s |b= var_e entry =/= null) /\
                     (s |b/= (var_e entry =/= var_e cptr)) /\
                     (s |b= var_e nptr == nat_e (get_endl (l1 ++ (size,stat)::nil) p))))))
   )
).

Decompose_hyp.
exists (nat_e (get_endl (x1 ++ (x2,x3)::nil) p)).
apply cell_read.
split.
rewrite H14 in H12.
generalize (hl_getnext _ _ _ _ _ _ _ H12); intros. 
Decompose_sepcon H11 h1 h2.
Compose_sepcon h1 (h2 +++ H2).
unfold next.
rewrite get_endl_app.
simpl get_endl.
Mapsto.
red; auto.
red.
exists x0.
split.
Compose_sepcon H1 H2.
eapply Heap_List_inde_store; apply H12.
Array_equiv.
split; auto.
split; auto.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
exists x1.
exists x2.
exists x3.
split.
exists x4.
split; auto.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
auto.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
split.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
auto.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.
auto.

Step TT.

Step (fun s h =>
     (exists l,
         Heap_List l p s h /\
         In_hl l (x, sizex, free) p /\
         In_hl l (y, sizey, statusy) p /\
         x <> y /\
         (s |b= var_e hmStart == nat_e p) /\
         (s |b= var_e cptr == nat_e x) /\
         (exists l1,
            (exists size,
               (exists stat,
                  (exists l2,
                     l = l1 ++ (size, stat) :: l2 /\
                     (s |b= var_e entry == nat_e (get_endl l1 p)) /\
                     ~ In_hl l1 (x, sizex, alloc) p) /\
                     (s |b= var_e entry =/= null) /\
                     (s |b/= (var_e entry =/= var_e cptr)) /\
                     (s |b= var_e nptr == nat_e (get_endl (l1 ++ (size,stat)::nil) p))))))
).


decompose [and] H1; clear H1.
inversion_clear H2.
decompose [and] H1; clear H1.
inversion_clear H10.
inversion_clear H1.
inversion_clear H9.
decompose [and] H1; clear H1.
inversion_clear H9.
decompose [and] H1; clear H1.

assert (s |b= var_e entry == nat_e x).
Omega_exprb.
assert (sizex = x2 /\ alloc = x3).
rewrite H9 in H5.
Decompose_sepcon H2 h1 h2.
rewrite H9 in H12.
Decompose_sepcon H12 h11 h12.
eapply (In_hl_match x1 x4 x2) with (startp := p).
cutrewrite (get_endl x1 p = x); auto.
assert (s |b= nat_e (get_endl x1 p) == nat_e x).
Omega_exprb.
simpl in H20.
generalize (Zeq_bool_true _ _ H20); intros.
OmegaZ.
inversion_clear H12.
subst x2 x3.

unfold status.

rewrite H9 in H2.
unfold alloc in H2.
assert (get_endl x1 p = x); auto.
assert (s |b= nat_e (get_endl x1 p) == nat_e x).
Omega_exprb.
simpl in H12.
generalize (Zeq_bool_true _ _ H12); intros.
OmegaZ.
rewrite <- H12 in H2.
generalize (hl_alloc2free x1 x4 sizex p s h H2); intro.
inversion_clear H16.

exists x2.
Decompose_sepcon H17 h1 h2.
Compose_sepcon h1 h2.
Mapsto.

Intro_sepimp h1' h'.
exists (x1 ++ (sizex,true)::x4).
split.
eapply H20.
split; [apply H19 | Mapsto].
auto.
split.

eapply (In_hl_or_app).
right.
simpl.
rewrite H12.
repeat rewrite <- beq_nat_refl.
rewrite bool_eq_refl.
simpl; auto.

split.

rewrite H9 in H4.
generalize (In_hl_app_or _ _ _ _ _ _ H4); intro X; inversion_clear X.
eapply (In_hl_or_app).
left; auto.
simpl in H23.
assert (get_endl x1 p <> y); intros.
omega.
rewrite (beq_dif_false _ _ H24) in H23.
simpl in H23.
eapply (In_hl_or_app).
right; simpl.
rewrite (beq_dif_false _ _ H24).
simpl.
auto.
split; auto.
split.
Omega_exprb.
split.
Omega_exprb.
exists x1; exists sizex; exists true.
split.
exists x4.
split; auto.
split.
Omega_exprb.
split.
Omega_exprb.
rewrite get_endl_app in H13.
simpl get_endl in H13.
rewrite get_endl_app.
simpl get_endl.
Omega_exprb.

Step TT.

intros.
red.
Decompose_hyp.
exists x0.
split.
eapply Heap_List_inde_store; apply H1.
split; auto.
split; auto.
rewrite <- expr_b_store_update_rewrite.
Omega_exprb.

Step TT.
red; intros.
Decompose_hyp.
assert (s |b= var_e nptr == null).
Omega_exprb.
rewrite get_endl_app in H18.
simpl get_endl in H18.
assert (s |b= nat_e (get_endl x1 p + 2 + x2) =/= null).
simpl.
cut (Zeq_bool (Z_of_nat (get_endl x1 p + 2 + x2)) 0 = false).
intros.
destruct ((Zeq_bool (Z_of_nat (get_endl x1 p + 2 + x2)) 0)).
inversion H17.
auto.
generalize (Zeq_bool_false (Z_of_nat (get_endl x1 p + 2 + x2)) 0); intro X; inversion_clear X.
apply H21.
intuition.
OmegaZ.
assert (s |b= nat_e (get_endl x1 p + 2 + x2) == null).
Omega_exprb.
Omega_exprb.

Step TT.
red; intros.
Decompose_hyp.
destruct x1.
simpl get_endl in H17.
assert (s |b= var_e entry =/= null).
Omega_exprb.
Omega_exprb.
destruct p0.
simpl get_endl in H17.
generalize (get_endl_gt x1 (p + 2 + n)); intro.
assert (s |b= var_e entry =/= null).
Omega_exprb.
Omega_exprb.
Qed.

