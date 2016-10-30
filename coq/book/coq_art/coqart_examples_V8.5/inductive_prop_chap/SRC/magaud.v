(* solution de Nicolas *)


Require Export Arith.

Set Implicit Arguments.

Section DecidableEqDep.

  Variable A : Type.

  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    eq_ind _ (fun a => a = y') eq2 _ eq1.

  Remark trans_sym_eq : forall (x y:A) (u:x = y), comp u u = refl_equal y.
intros.
case u; trivial.
Qed.



  Variable eq_dec : forall x y:A, x = y \/ x <> y.

  Variable x : A.


  Let nu (y:A) (u:x = y) : x = y :=
    match eq_dec x y with
    | or_introl eqxy => eqxy
    | or_intror neqxy => False_ind _ (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
intros.
unfold nu in |- *.
case (eq_dec x y); intros.
reflexivity.

case n; trivial.
Qed.


  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (refl_equal x)) v.


  Remark nu_left_inv : forall (y:A) (u:x = y), nu_inv (nu u) = u.
intros.
case u; unfold nu_inv in |- *.
apply trans_sym_eq.
Qed.


  Theorem eq_proofs_unicity : forall (y:A) (p1 p2:x = y), p1 = p2.
intros.
elim nu_left_inv with (u := p1).
elim nu_left_inv with (u := p2).
elim nu_constant with y p1 p2.
reflexivity.
Qed.

  Theorem K_dec :
   forall P:x = x -> Prop, P (refl_equal x) -> forall p:x = x, P p.
intros.
elim eq_proofs_unicity with x (refl_equal x) p.
trivial.
Qed.

End DecidableEqDep.

  (** We deduce the [K] axiom for (decidable) Set *)
  Theorem K_dec_set :
   forall A:Set,
     (forall x y:A, {x = y} + {x <> y}) ->
     forall (x:A) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
intros.
elim p using K_dec.
intros.
case (H x0 y); intros.
elim e; left; reflexivity.

right; red in |- *; intro neq; apply n; elim neq; reflexivity.

trivial.
Qed.

Section def.
Variable A:Set.

Inductive vect: nat -> Set :=
  vnil: vect O
| vcons:forall n:nat, A -> (vect n) -> (vect (S n)).

Lemma uniq : forall v:(vect 0), v=vnil.
intros v.
change (v= (eq_rec O vect vnil O (refl_equal O))).
generalize (refl_equal O).
change
  ((fun (n : nat) (v : vect n) =>
    forall e : 0 = n, v = eq_rec _ vect vnil _ e) 0 v)
 in |- * .
case v; intros.
apply K_dec_set with (p := e).
exact eq_nat_dec.
reflexivity.
discriminate e.
Qed.
End def.
