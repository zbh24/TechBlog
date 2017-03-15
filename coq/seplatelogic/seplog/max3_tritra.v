Load seplog_header.

Require Import Omega.

Require Import frag_list_triple.
Require Import frag_list_entail.

Require Import expr_b_dp.
Require Import Max.

(* with bigtoe *)

Notation "[[ P ]] c [[ Q ]]" := ({{ assrt_interp P }} c {{ Assrt_interp (Q::nil)}}) (at level 80).

Goal
  [[(true_b, emp)]]
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
  [[(((var_e 0) == (var_e 1)) ||| ((var_e 0) == (var_e 2)) ||| ((var_e 0) == (var_e 3)),emp)]].

  eapply tritra_use.
  simpl.
  eapply refl_equal.
  eapply tritra_if.
  eapply tritra_if.
  eapply tritra_subst_elt.
  simpl.
  eapply tritra_entail.
  eapply Decompose_Assrt_interp; left.
  eapply entail_soundness; Entail.
  eapply tritra_subst_elt.
  simpl.
  eapply tritra_entail.
  eapply Decompose_Assrt_interp; left.
  eapply entail_soundness; Entail.
  eapply tritra_if.
  eapply tritra_subst_elt.
  simpl.
  eapply tritra_entail.
  eapply Decompose_Assrt_interp; left.
  eapply entail_soundness; Entail.
  eapply tritra_subst_elt.
  simpl.
  eapply tritra_entail.
  eapply Decompose_Assrt_interp; left.
  eapply entail_soundness; Entail.
  Show Proof.
  (* proof size = 568 *)
Qed.
