Load seplog_header.

Require Import Omega.

Require Import frag_list_triple.
Require Import frag_list_entail.

Require Import expr_b_dp.
Require Import Max.

(* with bigtoe *)

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


(* with bigtoe *)

Lemma swap_verif': 
    {{assrt_interp (swap_precond x y vx vy)}}
    swap x y
    {{Assrt_interp ((swap_postcond x y vx vy)::nil)}}.
intros.
unfold swap_precond.
unfold swap_postcond.
eapply tritra_use.
simpl; intuition.
unfold x; unfold y; unfold i; unfold j; unfold vx; unfold vy.
unfold swap.
Rotate_tritra_sig_lhs.
eapply tritra_lookup.
unfold eval_pi; intros; Omega_exprb.
Rotate_tritra_sig_lhs.
eapply tritra_subst_lookup'.
unfold eval_pi; intros; Omega_exprb.
simpl; intuition.
eapply tritra_subst_mutation.
simpl.
Rotate_tritra_sig_lhs.
eapply tritra_mutation.
unfold eval_pi; intros; Omega_exprb.
eapply tritra_subst_mutation.
simpl.
Rotate_tritra_sig_lhs.
eapply tritra_mutation.
unfold eval_pi; intros; Omega_exprb.
eapply tritra_subst_elt.
simpl.
eapply tritra_entail.
eapply Decompose_Assrt_interp; left.
eapply entail_soundness; Entail.
Qed.
