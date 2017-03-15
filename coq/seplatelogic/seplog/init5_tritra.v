Load seplog_header.

Require Import Omega.

Require Import frag_list_triple.
Require Import frag_list_entail.

Require Import expr_b_dp.
Require Import Max.

(* with bigtoe *)

Notation "[[ P ]] c [[ Q ]]" := ({{ assrt_interp P }} c {{ Assrt_interp (Q::nil)}}) (at level 80).

(* initialization: initialize some field of an array of data-structure*)

Definition ptr : var.v := 1.
Definition startl : var.v := 2.
Definition size: var.v := 3.
Definition idx: var.v := 4.
Definition init_val: var.v := 5.

Fixpoint init_body (n: nat) {struct n}: cmd := 
  match n with
    0 => skip
    | S n' => 
      ((var_e ptr) +e (var_e idx)) *<- var_e init_val;
       ptr <- (var_e ptr) +e (var_e size);
       init_body n'
   end.

Definition init (n: nat) : cmd :=
    ptr <- var_e startl;
    init_body n.

Fixpoint init_precond_sigma (n: nat) {struct n} : Sigma :=
  match n with 
    0 => emp
    | S n' => star 
        (cell (((var_e startl) +e (var_e idx)) +e ((var_e size) *e (int_e (Z_of_nat n'))) )) 
	(init_precond_sigma n')
end. 

Definition init_precond (n: nat) : assrt :=
  (var_e startl >> int_e 0%Z, init_precond_sigma n).

Fixpoint init_postcond_sigma (n: nat) {struct n}: Sigma :=
  match n with 
    0 => emp
    | S n' => star 
	(singl (((var_e startl) +e (var_e idx)) +e ((var_e size) *e (int_e (Z_of_nat n'))) ) (var_e init_val)) 
	(init_postcond_sigma n')
end. 

Definition init_postcond (n: nat) : assrt :=
  (var_e startl >> int_e 0%Z, init_postcond_sigma n).

(* with bigtoe *)


Lemma init_verif_bigtoe_5: forall n,
    n = 5 -> 
    [[init_precond n]]
    (init n)
    [[(init_postcond n)]].

intros; subst n. 
unfold init; simpl init_body.
unfold init_precond; simpl init_precond_sigma.
unfold init_postcond; simpl init_postcond_sigma.
unfold ptr; unfold startl; unfold size; unfold idx; unfold init_val.

eapply tritra_use.
simpl; intuition.

Tritra.
Qed.
