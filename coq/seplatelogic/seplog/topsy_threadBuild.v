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

Open Local Scope Z_scope.
Open Local Scope vc_scope.


(* structure ProcContextPtr *)

Definition pcp_tf_gs := 0.
Definition pcp_tf_fs := 1.
Definition pcp_tf_es := 2.
Definition pcp_tf_ds := 3.
Definition pcp_tf_trapno := 4.
Definition pcp_tf_edi := 5.
Definition pcp_tf_esi := 6.
Definition pcp_tf_ebp := 7.
Definition pcp_tf_temp_esp := 8.
Definition pcp_tf_ebx := 9.
Definition pcp_tf_edx := 10.
Definition pcp_tf_ecx := 11.
Definition pcp_tf_eax := 12.
Definition pcp_tf_err := 13.
Definition pcp_tf_eip := 14.
Definition pcp_tf_cs := 15.
Definition pcp_tf_eflags := 16.
Definition pcp_tf_esp := 17.
Definition pcp_tf_ss := 18.

(* structure Thread *)

Definition th_contextPtr := 0.
Definition th_id := 1.
Definition th_name :=2.
Definition th_parentId := 3.
Definition th_stackStart := 4.
Definition th_stackEnd := 5.
Definition th_msgQueue := 6.
Definition th_schedInfo := 7.
Definition th_stat := 8.

(* structure *)

Close Local Scope Z_scope.

(* Definition *)

Definition USER : Z := 1%Z.
Definition KERNEL : Z := 0%Z.

Axiom sizeof_Message:nat.
Axiom exitCodeLength:nat.
Axiom MAXNAMESIZE : nat.
Axiom STATUS_INT_ENABLE_USER_PREV:nat.
Axiom STATUS_INT_ENABLE_KERNEL_PREV:nat.

Definition skip : cmd' := (0) <- (var_e 0).

(* Les subroutines *)

(*
void stringNCopy(char* target, char* source, unsigned long int size)
{
  while ((( *target++ = *source++) != '\0') && ((--size) > 1)) ;
  *target = '\0';
}
*)

Open Local Scope Z_scope.

(* tmp serves as a temporary buffer variable *)
Definition stringNCopy (tmp:nat) (target:nat) (source:nat) (size:nat) := 
  tmp <-* var_e source;
  var_e target *<- var_e tmp;
  size <- var_e size -e int_e 1%Z;
  while' ((var_e tmp == int_e 0) &&& (var_e size =/= int_e 0)) (TT) (
    tmp <-* var_e source;
    var_e target *<- var_e tmp;
    size <- var_e size -e int_e 1
  ).

(* La plus importante procedure: l'inititalisation des champs pour les registres *)
(* tmSetMachineDependentRegisters *)

Definition tmSetMachineDependentRegisters (context_ptr space:nat) :=
  ifte (var_e space == int_e USER) thendo (
    (context_ptr -.> pcp_tf_cs) *<- int_e 3;
    (context_ptr -.> pcp_tf_ds) *<- int_e 3;
    (context_ptr -.> pcp_tf_es) *<- int_e 3;
    (context_ptr -.> pcp_tf_fs) *<- int_e 3;
    (context_ptr -.> pcp_tf_gs) *<- int_e 3;
    (context_ptr -.> pcp_tf_ss) *<- int_e 3
  ) elsedo (
    (context_ptr -.> pcp_tf_cs) *<- int_e 0;
    (context_ptr -.> pcp_tf_ds) *<- int_e 0;
    (context_ptr -.> pcp_tf_es) *<- int_e 0;
    (context_ptr -.> pcp_tf_fs) *<- int_e 0;
    (context_ptr -.> pcp_tf_gs) *<- int_e 0;
    (context_ptr -.> pcp_tf_ss) *<- int_e 0
  ) .

Definition precond (cs0 ds0 es0 fs0 gs0 ss0:expr) (context_ptr space:var.v) := fun s h => 
  eval (var_e space) s = USER /\ (
    (context_ptr -.> pcp_tf_cs |-> cs0) **
    (context_ptr -.> pcp_tf_ds |-> ds0) **
    (context_ptr -.> pcp_tf_es |-> es0) **
    (context_ptr -.> pcp_tf_fs |-> fs0) **
    (context_ptr -.> pcp_tf_gs |-> gs0) **
    (context_ptr -.> pcp_tf_ss |-> ss0)) s h.

Definition postcond (context_ptr space:var.v) := 
  (context_ptr -.> pcp_tf_cs |-> int_e 3) **
  (context_ptr -.> pcp_tf_ds |-> int_e 3) **
  (context_ptr -.> pcp_tf_es |-> int_e 3) **
  (context_ptr -.> pcp_tf_fs |-> int_e 3) **
  (context_ptr -.> pcp_tf_gs |-> int_e 3) **
  (context_ptr -.> pcp_tf_ss |-> int_e 3) .

Definition threadBuild 
(* variables pour stringNCopy *)
  (stringNCopy_source:nat) (stringNCopy_target:nat) (stringNCopy_size:nat)
(* variable tampon *)
  (tmp:nat)
(* variables locales *)
  (sp:nat) (mode:nat)
(* parameters *)
  (id:nat) (parentId:nat) (name:nat) (contextPtr:nat) (stackBaseAddress:nat)
  (stackSize:nat) (mainFunction:nat) (parameter:nat) (space:nat) (threadPtr:nat) (priority:nat) :=

  (threadPtr -.> th_id) *<- var_e id;
  (threadPtr -.> th_parentId) *<- var_e parentId;
  ifte (var_e name =/= int_e 0) thendo (
    stringNCopy_source <-* (threadPtr -.> th_name);
    stringNCopy_target <- var_e name;
    stringNCopy_size <- int_e (Z_of_nat MAXNAMESIZE);
    stringNCopy tmp stringNCopy_source stringNCopy_target stringNCopy_size)
  elsedo (
    stringNCopy_source <-* (threadPtr -.> th_name);
           (* putain je fais comment pour placer ca ... "no name" ... *)
    stringNCopy tmp stringNCopy_source stringNCopy_target stringNCopy_size);
(* initMsgQueue*)
  ifte (var_e space == int_e USER) thendo (
    skip;
    mode <- int_e (Z_of_nat STATUS_INT_ENABLE_USER_PREV)) 
  elsedo (
    skip;
    mode <- int_e (Z_of_nat STATUS_INT_ENABLE_KERNEL_PREV));
  (threadPtr -.> th_stackStart) *<- var_e stackBaseAddress +e var_e stackSize -e int_e 4;
  (threadPtr -.> th_stackEnd) *<- var_e stackBaseAddress;
  (threadPtr -.> th_contextPtr) *<- var_e contextPtr;
(* tmSetMachineDependentRegisters *)
  tmp <-* (threadPtr -.> th_stackStart);
  sp <- var_e tmp -e int_e (Z_of_nat sizeof_Message) -e int_e (Z_of_nat exitCodeLength)
(* tmSetStackPointer *)
.

Close Local Scope vc_scope.

Lemma false_imp : forall c P, {{ FF }} c {{ P }}.
induction c.
intro.
apply semax_strengthen_pre with (P).
red.
contradiction.
apply semax_skip.
intro.
apply semax_strengthen_pre with (update_store2 v e P).
red.
contradiction.
apply semax_assign_var_e.
intro.
apply semax_strengthen_pre with (lookup2 v e P).
red.
contradiction.
apply semax_assign_var_lookup.
intro.
apply semax_strengthen_pre with (update_heap2 e e0 P).
red.
contradiction.
apply semax_assign_lookup_expr.
intro.
apply semax_strengthen_pre with (fun s h => forall n, 
  ((n |-> e) -* update_store2 v n P) s h).
red.
contradiction.
apply semax_malloc.
intros.
apply semax_strengthen_pre with (fun s h =>
      exists l, val2loc (eval e s) = Some l /\
        exists v, heap.lookup l h = Some v /\
          P s (heap.dif h l)).
red.
contradiction.
apply semax_free.
intro.
apply semax_weaken_post with (fun s h => (
(fun s' h' => (P s' h')/\(eval_b e s')=false) s h
) /\ (eval_b e s)=false).
red.
intuition.
apply semax_strengthen_pre with (fun s h => (P s h)/\(eval_b e s)=false).
red.
contradiction.
apply (semax_while (fun s h => (P s h)/\(eval_b e s)=false) e c).
apply semax_strengthen_pre with FF.
red.
intros.
inversion_clear H.
inversion_clear H0.
rewrite H1 in H2; discriminate H2.
apply IHc.
intros.
apply semax_seq with FF.
apply IHc1.
apply IHc2.
intros.
apply semax_ifte.
apply semax_strengthen_pre with FF.
red.
intuition.
apply IHc1.
apply semax_strengthen_pre with FF.
red.
intuition.
apply IHc2.
Qed.

Lemma tmSetMachineDependentRegisters_Lemma: forall (cs0 ds0 es0 fs0 gs0 ss0:expr),
  forall (context_ptr space:var.v), (var.set (context_ptr::space::nil)) ->
    {{ (precond cs0 ds0 es0 fs0 gs0 ss0) context_ptr space}}
    proj_cmd (tmSetMachineDependentRegisters context_ptr space)
    {{ postcond context_ptr space}}.
intros.
unfold tmSetMachineDependentRegisters.
simpl.
apply semax_ifte.
apply semax_strengthen_pre with (precond cs0 ds0 es0 fs0 gs0 ss0 context_ptr space).
red.
intuition.
unfold precond.
unfold postcond.

apply semax_strengthen_pre with (
(((((((context_ptr -.> pcp_tf_cs) |-> cs0) **
          ((context_ptr -.> pcp_tf_ds) |-> ds0)) **
         ((context_ptr -.> pcp_tf_es) |-> es0)) **
        ((context_ptr -.> pcp_tf_fs) |-> fs0)) **
       ((context_ptr -.> pcp_tf_gs) |-> gs0)) **
      ((context_ptr -.> pcp_tf_ss) |-> ss0))
).
red.
intros.
intuition.

eapply semax_seq.

rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.

apply frame_rule.
apply semax_assign_lookup_expr_local.
red; simpl; contradiction.

eapply semax_seq.

rewrite sep.con_com_equiv.
rewrite sep.con_assoc_equiv.
apply frame_rule.
apply semax_assign_lookup_expr_local.
red; simpl; contradiction.

eapply semax_seq.

rewrite sep.con_com_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.

apply frame_rule.
apply semax_assign_lookup_expr_local.
red; simpl; contradiction.

eapply semax_seq.

rewrite sep.con_com_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.

apply frame_rule.
apply semax_assign_lookup_expr_local.
red; simpl; contradiction.

eapply semax_seq.

rewrite sep.con_com_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.

apply frame_rule.
apply semax_assign_lookup_expr_local.
red; simpl; contradiction.

rewrite sep.con_com_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.

pattern (((((((context_ptr -.> pcp_tf_cs) |-> int_e 3) **
         ((context_ptr -.> pcp_tf_ds) |-> int_e 3)) **
        ((context_ptr -.> pcp_tf_es) |-> int_e 3)) **
       ((context_ptr -.> pcp_tf_fs) |-> int_e 3)) **
      ((context_ptr -.> pcp_tf_gs) |-> int_e 3)) **
     ((context_ptr -.> pcp_tf_ss) |-> int_e 3)).

rewrite sep.con_com_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.
rewrite sep.con_assoc_equiv.

apply frame_rule.
apply semax_assign_lookup_expr_local.
red; simpl; contradiction.
unfold precond.
simpl.
apply semax_strengthen_pre with FF.
red.
intros.
decompose [and] H0; clear H0.
rewrite H3 in H2.
rewrite (Zeq_bool_refl USER) in H2; discriminate H2.
apply false_imp.
Qed.

