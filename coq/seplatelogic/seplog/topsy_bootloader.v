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

Open Local Scope sep_scope.
Open Local Scope vc_scope.

Definition GDTxSIZE : nat := 8*5.
Axiom GDT00: nat.
Definition GDT_BASE: var.v := 16.
Definition GDTSEG: nat :=0.
Definition GDTOF: nat := 1000.

Definition es:var.v := 0.
Definition ds:var.v := 1.
Definition di:var.v := 2.
Definition si:var.v := 3.
Definition ax:var.v := 4.
Definition cx:var.v := 5.
Definition df:var.v := 6.

Axiom dec_sel: nat.

(* semantique de l'instruction movsw en seplog *)
Definition movsw (tmp:var.v) :=
(* [es:di] <- [ds:si] *)
(tmp <-* ((var_e ds) *e (int_e (Z_of_nat dec_sel)) +e (var_e si)));
(((var_e es) *e (int_e (Z_of_nat dec_sel)) +e (var_e di)) *<- (var_e tmp));
(* increment *)
(di <- (var_e di) +e (int_e 1%Z));
(si <- (var_e si) +e (int_e 1%Z));
(* rebelote *)
(tmp <-* ((var_e ds) *e (int_e (Z_of_nat dec_sel)) +e (var_e si)));
(((var_e es) *e (int_e (Z_of_nat dec_sel)) +e (var_e di)) *<- (var_e tmp));
(di <- (var_e di) +e (int_e 1%Z));
(si <- (var_e si) +e (int_e 1%Z)).

Definition createGDT (tmp:var.v) :=

(* remplissage de es via ax *)
(ax <- (int_e (Z_of_nat GDTSEG)));
(es <- (var_e ax));
(* rebelote *)
(ax <- (int_e (Z_of_nat GDTOF)));
(di <- (var_e ax));
(* taille de la GDT en bytes, divisee par deux (parce que movsw copie 2x2) *)
(cx <- (int_e (Z_of_nat GDTxSIZE)));
(cx <- (div_e (var_e cx) (int_e 2%Z)));
(ax <- (int_e (Z_of_nat GDT00)));
(si <- (var_e ax));
(* df est un champ de ef *)
(df <- (int_e 0%Z));
while' ((var_e cx) >> (int_e 0%Z)) (TT)
(
 movsw (tmp);
 cx <- (var_e cx) -e (nat_e 1)
)
.

Definition GDTptr := GDTOF.
Axiom IDTptr : nat.

Definition idtr:var.v := 7.
Definition gdtr:var.v := 8.
Definition eax:var.v := 9.
Definition cr0:var.v := 10.
Definition bx:var.v := 11.
Definition fs:var.v := 12.
Definition gs:var.v := 13.
Definition ss:var.v := 14.
Definition esp:var.v := 15.

Axiom gOSData_Sel: nat.
Axiom OSD_SIZE:nat.


Definition PM_Switch :=
(idtr <- (int_e (Z_of_nat IDTptr)));
(gdtr <- (int_e (Z_of_nat GDTptr)));
(eax <- (int_e 1%Z));
(cr0 <- (var_e eax));
(bx <- (int_e (Z_of_nat gOSData_Sel)));
(ds <- (var_e bx));
(es <- (var_e bx));
(fs <- (var_e bx));
(gs <- (var_e bx));
(ss <- (var_e bx));
(eax <- (int_e (Z_of_nat OSD_SIZE)));
(esp <- (var_e eax)).



Import valandloc.

Axiom memory_size: nat.

Open Local Scope Z_scope.

Definition p2_14 := Zpower 2 14.
Definition p2_24 := Zpower 2 24.
Definition p2_16 := Zpower 2 16.
Definition p2_8 := Zpower 2 8.

Axiom b_and : Z -> Z -> Z.

Definition Valid_Segment_Descriptor (x:loc) := fun s => fun h => 
  exists y0, exists y1, exists y2, exists y3, exists y4, exists y5, exists y6, exists y7,
    (((int_e (Z_of_nat x))|-->
      ((int_e y0)::(int_e y1)::(int_e y2)::(int_e y3)::(int_e y4)::(int_e y5)::(int_e y6)::(int_e y7)::nil)) ** TT) s h /\
    ((b_and (Zdiv y5 32) 3 = 0) \/ 
      ((y2 + (y3 * p2_8) + (y4 * p2_16) + (y7 * p2_24)) >= p2_14)).

Close Local Scope Z_scope.

Lemma Valid_Segment_descriptor_inde_store: forall s s' h x,
   Valid_Segment_Descriptor x s h -> Valid_Segment_Descriptor x s' h.
trivial.
Qed.

Ltac Resolve_simpl:=
   match goal with

      | id: Array ?adr ?size ?s ?h |- Array ?adr ?size ?s2 ?h =>
                 eapply Array_inde_store; apply id

      | |- eval (var_e ?v) (store.update ?v ?p ?s) = ?p1 => simpl; rewrite store.lookup_update'; auto
      
      | id: eval (var_e ?v) ?s = ?p |- eval (var_e ?v) (store.update ?v' ?p' ?s) = ?p =>
                 simpl; rewrite <- store.lookup_update; [auto | unfold v; unfold v'; omega]
   end.


Axiom coucou: False.
Ltac Coucou := generalize coucou; contradiction.


Axiom Array_ouch1: forall adr bloc_size bloc_num s h,
  ((Array adr (bloc_num * bloc_size) ** TT) s h) ->
  (forall x, x>= 0 /\ x< bloc_num -> ((Array (adr + x * bloc_size) bloc_size ) ** TT) s h).

Lemma bootloader_verif: forall tmp,
  {{ fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (GDT00 + x* 8) s h) }}

  (proj_cmd (createGDT tmp; PM_Switch))

  {{ fun s => fun h => (eval (var_e cr0) s) = 1%Z  /\
    ( forall p, eval (var_e gdtr) s = Z_of_nat p -> 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (p + x* 8) s h)) 
    }}.

Close Local Scope vc_scope.

intros.
unfold createGDT; unfold PM_Switch.
simpl proj_cmd.
apply semax_seq with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (1000 + x* 8) s h)).

apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (GDT00 + x* 8) s h) /\
    (eval (var_e ax) s = 0%Z)
).
red; red; intuition.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (GDT00 + x* 8) s h) /\
    (eval (var_e ax) s = 0%Z) /\
    (eval (var_e es) s = 0%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (GDT00 + x* 8) s h) /\
    (eval (var_e ax) s = 1000%Z) /\
    (eval (var_e es) s = 0%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (GDT00 + x* 8) s h) /\
    (eval (var_e ax) s = 1000%Z) /\
    (eval (var_e di) s = 1000%Z) /\
    (eval (var_e es) s = 0%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (GDT00 + x* 8) s h) /\
    (eval (var_e ax) s = 1000%Z) /\
    (eval (var_e di) s = 1000%Z) /\
    (eval (var_e cx) s = 40%Z) /\
    (eval (var_e es) s = 0%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (GDT00 + x* 8) s h) /\
    (eval (var_e ax) s = 1000%Z) /\
    (eval (var_e di) s = 1000%Z) /\
    (eval (var_e cx) s = 20%Z) /\
    (eval (var_e es) s = 0%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
simpl in H3; rewrite H3.
intuition.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (GDT00 + x* 8) s h) /\
    (eval (var_e ax) s = (Z_of_nat GDT00)) /\
    (eval (var_e di) s = 1000%Z) /\
    (eval (var_e cx) s = 20%Z) /\
    (eval (var_e es) s = 0%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (GDT00 + x* 8) s h) /\
    (eval (var_e ax) s = (Z_of_nat GDT00)) /\
    (eval (var_e si) s = (Z_of_nat GDT00)) /\
    (eval (var_e di) s = 1000%Z) /\
    (eval (var_e cx) s = 20%Z) /\
    (eval (var_e es) s = 0%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (GDT00 + x* 8) s h) /\
    (eval (var_e ax) s = (Z_of_nat GDT00)) /\
    (eval (var_e si) s = (Z_of_nat GDT00)) /\
    (eval (var_e di) s = 1000%Z) /\
    (eval (var_e cx) s = 20%Z) /\
    (eval (var_e es) s = 0%Z) /\
    (eval (var_e df) s = 0%Z) 
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
apply semax_while' with 
  (* taille de la gdt en bytes *)
  (fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
  (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (GDT00 + x* 8) s h) /\
  (* cx contient le nombre d'octets a copier / 2 *)
  (* pour chaque offset p, le contenu de la gdt est ident. au contenu de la data struct. en 1000 *)
  (forall p, (40 - ((eval (var_e cx) s)) * 2)%Z = (Z_of_nat p) -> 
    (forall x, x >= 0 /\ x < p -> (heap.lookup  (GDT00 + x) h = heap.lookup (1000 + x) h) )) /\
  (* di/si sont les offsets *)
  (eval (var_e si) s = ((Z_of_nat GDT00) + (40 - ((eval (var_e cx) s)) * 2)))%Z /\
  (eval (var_e di) s = (1000%Z + (40 - ((eval (var_e cx) s)) * 2)))%Z /\
  (eval (var_e cx) s >= 0%Z)%Z /\
  (eval (var_e es) s = 0%Z) /\
  (eval (var_e df) s = 0%Z) 
).

Coucou.


apply semax_seq with (fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
  (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (GDT00 + x* 8) s h) /\
  (* cx contient le nombre d'octets a copier / 2 *)
  (* pour chaque offset p, le contenu de la gdt est ident. au contenu de la data struct. en 1000 *)
  (forall p, (40 - ((eval (var_e cx) s)) * 2)%Z = (Z_of_nat p) -> 
    (forall x, x >= 0 /\ x < p+1 -> (heap.lookup  (GDT00 + x) h = heap.lookup (1000 + x) h) )) /\
  (* di/si sont les offsets *)
  (eval (var_e si) s = ((Z_of_nat GDT00) + (40 - ((eval (var_e cx) s)) * 2)))%Z /\
  (eval (var_e di) s = (1000%Z + (40 - ((eval (var_e cx) s)) * 2)))%Z /\
  (eval (var_e cx) s >= 0%Z)%Z /\
  (eval (var_e es) s = 0%Z) /\
  (eval (var_e df) s = 0%Z) 
).

Coucou.

apply semax_assign_var_e'.

Coucou.
Coucou.

(* PM switch *)

(* initialize gdtr et met cr0 a 1 *)

apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (1000 + x* 8) s h)
).
red; red; intuition.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (1000 + x* 8) s h) /\
    (eval (var_e gdtr) s = 1000%Z) 
).
red; red; intuition.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (1000 + x* 8) s h) /\
    (eval (var_e gdtr) s = 1000%Z) /\
    (eval (var_e eax) s = 1%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (1000 + x* 8) s h) /\
    (eval (var_e gdtr) s = 1000%Z) /\
    (eval (var_e eax) s = 1%Z) /\
    (eval (var_e cr0) s = 1%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (1000 + x* 8) s h) /\
    (eval (var_e gdtr) s = 1000%Z) /\
    (eval (var_e cr0) s = 1%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (1000 + x* 8) s h) /\
    (eval (var_e gdtr) s = 1000%Z) /\
    (eval (var_e cr0) s = 1%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (1000 + x* 8) s h) /\
    (eval (var_e gdtr) s = 1000%Z) /\
    (eval (var_e cr0) s = 1%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (1000 + x* 8) s h) /\
    (eval (var_e gdtr) s = 1000%Z) /\
    (eval (var_e cr0) s = 1%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (1000 + x* 8) s h) /\
    (eval (var_e gdtr) s = 1000%Z) /\
    (eval (var_e cr0) s = 1%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (1000 + x* 8) s h) /\
    (eval (var_e gdtr) s = 1000%Z) /\
    (eval (var_e cr0) s = 1%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'' with ( fun s => fun h => ((Array GDTOF (5*8)) ** TT) s h /\ 
    (forall x, x >= 0 /\ x < 5 -> Valid_Segment_Descriptor (1000 + x* 8) s h) /\
    (eval (var_e gdtr) s = 1000%Z) /\
    (eval (var_e cr0) s = 1%Z)
).
red; red; intuition.
Resolve_simpl.
Resolve_simpl.
apply semax_assign_var_e'.
red.
intros.
red; intuition.
Resolve_simpl.
simpl in H2.
rewrite <- (store.lookup_update) in H2; [idtac | unfold eax; unfold esp; unfold gdtr;intuition].
simpl in H1; rewrite H1 in H2.
assert (1000%Z = Z_of_nat 1000).
intuition.
rewrite H4 in H2.
rewrite <- (Z_of_nat_inj _ _ H2).
apply Valid_Segment_descriptor_inde_store with s.
apply H.
intuition.
Qed.

