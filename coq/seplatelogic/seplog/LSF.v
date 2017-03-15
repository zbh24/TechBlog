Load seplog_header.

Require Import Omega.

Require Import frag_list_triple.
Require Import frag_list_entail.

Require Import expr_b_dp.
Require Import Max.

Import Fresh.

(*******************************************************************************)
(* Smallfoot like proof-system (pure forward) with arithmetic                  *)
(*******************************************************************************)

Inductive LSF : assrt -> cmd -> assrt -> Prop :=

  | LSF_precond_stre: forall L1 L1' L2 c,
    (assrt_interp L1) ==> (assrt_interp L1') -> 
    LSF L1' c L2 ->
    LSF L1 c L2

  | LSF_seq_assoc: forall P Q c1 c2 c3,
    LSF P (c1; (c2; c3)) Q ->
    LSF P ((c1; c2); c3) Q

  | LSF_add_empty: forall P Q c,
    LSF P (c; skip) Q ->
    LSF P c Q

  | LSF_empty: forall P Q,
    ((assrt_interp P) ==> (assrt_interp Q)) ->
    LSF P skip Q

  | LSF_assign: forall pi sig Q c x e x',
    fresh_assrt x' (pi, sig) ->
    fresh_assrt x' Q ->
    fresh_cmd x' c ->
    fresh_e x' e ->
    fresh_e x' (var_e x) ->
    LSF (((expr_b_rewrite pi (var_e x) (var_e x')) &&& ((var_e x) == (expr_rewrite e (var_e x) (var_e x')))), subst_Sigma sig x (var_e x')) c Q ->
    LSF (pi, sig) (x <- e ; c) Q

  | LSF_lookup: forall pi sig e1 e2 e x Q c x', 
    (forall s, eval_b pi s = true -> eval_b (e1 == e) s = true) ->
    fresh_assrt x' (pi, star sig (singl e1 e2)) ->
    fresh_assrt x' Q ->
    fresh_cmd x' c ->
    fresh_e x' e ->
    fresh_e x' (var_e x) ->
    LSF (((expr_b_rewrite pi (var_e x) (var_e x')) &&& ((var_e x) == (expr_rewrite e2 (var_e x) (var_e x')))), subst_Sigma (star sig (singl e1 e2)) x (var_e x')) c Q ->
    LSF (pi,star sig (singl e1 e2)) (x <-* e; c) Q

  | LSF_mutation: forall pi1 sig1 e1 e2 e3 e4 Q c, 
    (forall s, eval_b pi1 s = true -> eval_b (e1 == e3) s = true) ->
    LSF (pi1,star sig1 (singl e1 e4)) c Q ->
    LSF (pi1,star sig1 (singl e1 e2)) (e3 *<- e4 ; c) Q
    
  | LSF_mutation': forall pi1 sig1 e1 e3 e4 Q c, 
    (forall s, eval_b pi1 s = true -> eval_b (e1 == e3) s = true) ->
    LSF (pi1,star sig1 (singl e1 e4)) c Q ->
    LSF (pi1,star sig1 (cell e1)) (e3 *<- e4 ; c) Q

  | LSF_cond: forall b c1 c2 c Q pi sig,
    LSF (pi &&& b, sig) (c1;c) Q ->
    LSF (pi &&& (! b), sig) (c2;c) Q ->
    LSF (pi, sig) (ifte b thendo c1 elsedo c2; c) Q

  | LSF_unroll_lst_lookup: forall pi sig e1 e2 e x Q c x', 
    (forall s, eval_b pi s = true -> eval_b (e1 == e) s = true) ->
    fresh_assrt x' (pi, star sig (lst e1 e2)) ->
    fresh_assrt x' Q ->
    fresh_cmd x' c ->
    fresh_e x' e ->
    fresh_e x' (var_e x) ->
    (forall s, s |b= (pi =b> (e1 =/= e2))) ->
    LSF ((pi &&& ((var_e x') == e2) ,star sig (star (star (singl e1 (var_e x')) (cell (e1 +e (nat_e 1)))) (lst (var_e x') e2)))) (x <-* e; c) Q ->
    LSF ((pi &&& ((var_e x') =/= e2) ,star sig (star (star (singl e1 (var_e x')) (cell (e1 +e (nat_e 1)))) (lst (var_e x') e2)))) (x <-* e; c) Q ->
    LSF (pi,star sig (lst e1 e2)) (x <-* e; c) Q.

Axiom LSF_sound: forall P c Q,
  LSF P c Q ->
  {{assrt_interp P}} c {{assrt_interp Q}}.

Axiom LSF_lookup': forall pi sig e1 e2 e x Q c x', 
    (forall s, eval_b pi s = true -> eval_b (e1 == e) s = true) ->
    x' = (max (var_max_cmd c) (max (var_max_assrt (pi,star sig (singl e1 e2))) (max (var_max_assrt Q) (max x (var_max_expr e))))) + 1 ->
    LSF (((expr_b_rewrite pi (var_e x) (var_e x')) &&& ((var_e x) == (expr_rewrite e2 (var_e x) (var_e x')))), subst_Sigma (star sig (singl e1 e2)) x (var_e x')) c Q ->
    LSF (pi,star sig (singl e1 e2)) (x <-* e; c) Q.

Axiom LSF_assign': forall pi sig Q c x e x',
    x' = (max (var_max_cmd c) (max (var_max_assrt (pi,sig)) (max (var_max_assrt Q) (max x (var_max_expr e))))) + 1 ->
    LSF (((expr_b_rewrite pi (var_e x) (var_e x')) &&& ((var_e x) == (expr_rewrite e (var_e x) (var_e x')))), subst_Sigma sig x (var_e x')) c Q ->
    LSF (pi, sig) (x <- e ; c) Q.

Axiom LSF_unroll_lst_lookup': forall pi sig e1 e2 e x Q c x', 
    (forall s, eval_b pi s = true -> eval_b (e1 == e) s = true) ->
    x' = (max (var_max_cmd c) (max (var_max_assrt (pi,star sig (lst e1 e2))) (max (var_max_assrt Q) (max x (var_max_expr e))))) + 1 ->
    (forall s, s |b= (pi =b> (e1 =/= e2))) ->
    LSF ((pi &&& ((var_e x') == e2), star sig (star (star (singl e1 (var_e x')) (cell (e1 +e (nat_e 1)))) (lst (var_e x') e2)))) (x <-* e; c) Q ->
    LSF ((pi &&& ((var_e x') =/= e2), star sig (star (star (singl e1 (var_e x')) (cell (e1 +e (nat_e 1)))) (lst (var_e x') e2)))) (x <-* e; c) Q ->
    LSF (pi,star sig (lst e1 e2)) (x <-* e; c) Q.

(* oui mais la c'est une expression qui est introduite, comment introduire une variable ??? *)

(* bete test, pas si bete que ca finalement *)

Notation "[[ P ]] c [[ Q ]]" := ({{ assrt_interp P }} c {{ Assrt_interp (Q::nil)}}) (at level 80).

Ltac Rotate_LSF_sig_lhs :=
  match goal with
    | |- LSF (?pi,?sig) ?c ?Q =>
      eapply LSF_precond_stre with (
        (pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp) )
      ); [apply entail_soundness; simpl; Entail| simpl]
  end.
