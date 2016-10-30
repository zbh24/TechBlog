Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Require Export log2_it.
 
Inductive log_domain : nat ->  Prop :=
  log_domain_1: log_domain 1
 | log_domain_2:
     forall (p : nat), log_domain (S (div2 p)) ->  log_domain (S (S p)) .
 
Theorem log_domain_non_O: forall (x : nat), log_domain x ->  (x <> 0).
Proof.
intros x H; case H; intros; discriminate.
Qed.
 
Theorem log_domain_inv:
 forall (x p : nat), log_domain x -> x = S (S p) ->  log_domain (S (div2 p)).
Proof.
intros x p H; case H; (try (intros H'; discriminate H')).
intros p' H1 H2; injection H2; intros H3; rewrite <- H3; assumption.
Defined.
 
Fixpoint two_power (n : nat) : nat :=
 match n with O => 1 | S p => 2 * two_power p end.
 
Theorem spec_1:  two_power 0 <= 1 < 2 * two_power 0 .
simpl; auto with arith.
Qed.
 
Theorem spec_2:
 forall p v',
 ( two_power v' <= div2 (S (S p)) < 2 * two_power v' ) ->
  ( two_power (S v') <= S (S p) < 2 * two_power (S v') ).
intros p v' H; (cbv zeta iota beta delta [two_power]; fold two_power).
elim (div2_eq (S (S p))).
intros; omega.
intros; omega.
Qed.
 
Definition log_well_spec:
 forall x (h : log_domain x),
  ({v : nat |  two_power v <= x < 2 * two_power v }).
refine (fix
        log_well_spec (x : nat) (h : log_domain x) {struct h} :
          {v : nat |  two_power v <= x < 2 * two_power v } :=
           match x as y
           return x = y ->  ({v : nat |  two_power v <= y < 2 * two_power v })
           with
              0 =>
                fun h' =>
                False_rec
                 ({v : nat |  two_power v <= 0 < 2 * two_power v })
                 (log_domain_non_O x h h')
             | 1 =>
                 fun h' =>
                 exist (fun v =>  two_power v <= 1 < 2 * two_power v ) 0 spec_1
             | S (S p) =>
                 fun h' =>
                    match log_well_spec (S (div2 p)) (log_domain_inv x p h h')
                     with
                      exist _ v' Hv' =>
                        exist 
                         (fun v =>  two_power v <= S (S p) < 2 * two_power v )
                         (S v') (spec_2 p v' Hv')
                    end
           end (refl_equal x)).
Qed.
