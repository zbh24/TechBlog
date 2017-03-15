Load seplog_header.

Require Import Omega.

Require Import frag_list_triple.
Require Import frag_list_entail.

Require Import expr_b_dp.
Require Import Max.

Import Fresh.

Require Import LSF.

(* swap: swap the value of two cells *)

Definition i : var.v := 1.
Definition j : var.v := 2.
Definition x : var.v := 4.
Definition y : var.v := 3.
Definition vx : var.v := 5.
Definition vy : var.v := 6.

Definition swap (x y:var.v) : cmd :=
    i <-* var_e x;
    j <-* var_e y;
    var_e x *<- var_e j;
    var_e y *<- var_e i.

Definition swap_precond (x y:var.v) (vx vy : nat) : assrt := 
  (true_b, star (singl (var_e x) (var_e vx)) (singl (var_e y) (var_e vy))).

Definition swap_postcond (x y:var.v) (vx vy : nat) : assrt := 
  (true_b, star (singl (var_e x) (var_e vy)) (singl (var_e y) (var_e vx))).

(* with smallfoot *)


Ltac Rotate_LSF_sig_lhs :=
  match goal with
    | |- LSF (?pi,?sig) ?c ?Q =>
      eapply LSF_precond_stre with (
        (pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp) )
      ); [apply entail_soundness; simpl; Entail| simpl]
  end.

Lemma swap_verif: 
    {{assrt_interp (swap_precond x y vx vy)}}
    swap x y
    {{assrt_interp ((swap_postcond x y vx vy))}}.
  intros.
  unfold swap_precond.
  unfold swap_postcond.
  eapply LSF_sound.
  simpl; intuition.
  unfold x; unfold y; unfold i; unfold j; unfold vx; unfold vy.
  unfold swap.
  eapply LSF_add_empty.
  repeat (eapply LSF_seq_assoc).
  Rotate_LSF_sig_lhs.
  eapply LSF_lookup'.
  intros; Omega_exprb.
  simpl; intuition.
  simpl.
  repeat (eapply LSF_seq_assoc).
  Rotate_LSF_sig_lhs.
  eapply LSF_lookup'.
  intros; Omega_exprb.
  simpl; intuition.
  repeat (eapply LSF_seq_assoc).  
  simpl.
  Rotate_LSF_sig_lhs.
  eapply LSF_mutation.
  intros; Omega_exprb.
  Rotate_LSF_sig_lhs.
  eapply LSF_mutation.
  intros; Omega_exprb.
  eapply LSF_empty.
  eapply entail_soundness.
  Entail.
Qed.
