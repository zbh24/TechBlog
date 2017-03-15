Load seplog_header.

Require Import Omega.

Require Import frag_list_triple.
Require Import frag_list_entail.

Require Import expr_b_dp.
Require Import Max.

Import Fresh.

Require Import LSF.

(* max3: return the max of three variable*)

(* with small foot *)
Goal
  {{ assrt_interp (true_b, emp)}}
  ifte ((var_e 1) >>= (var_e 2)) thendo
    ifte ((var_e 1) >>= (var_e 3)) thendo
      (0 <- (var_e 1))
    elsedo
      (0 <- (var_e 3))
  elsedo
    ifte ((var_e 2) >>= (var_e 3)) thendo
      (0 <- (var_e 2))
    elsedo
      (0 <- (var_e 3))
  {{ assrt_interp (((var_e 0) == (var_e 1)) ||| ((var_e 0) == (var_e 2)) ||| ((var_e 0) == (var_e 3)), emp)}}.
  eapply LSF_sound.
  eapply LSF_add_empty.
  eapply LSF_cond.
  eapply LSF_cond.
  eapply LSF_assign'.
  simpl; apply refl_equal.
  simpl.
  eapply LSF_empty.

  eapply entail_soundness; Entail.

  eapply LSF_assign'.
  simpl; apply refl_equal.
  simpl.
  eapply LSF_empty.
  eapply entail_soundness; Entail.
  eapply LSF_cond.
  eapply LSF_assign'.
  simpl; apply refl_equal.
  simpl.
  eapply LSF_empty.
  eapply entail_soundness; Entail.
  eapply LSF_assign'.
  simpl; apply refl_equal.
  simpl.
  eapply LSF_empty.
  eapply entail_soundness; Entail.
  Show Proof.
  (* proof size = 545 *)
Qed.
