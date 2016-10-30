Require Export Arith.
Require Export ArithRing.
Require Export ZArith.

Fixpoint fib (n:nat) : nat :=
  match n with
    0 => 1
  | 1 => 1
  | S ((S p) as q) => fib p + fib q
  end.

Theorem fib_ind :
  forall P : nat -> Prop,
    P 0 -> P 1 ->
    (forall n, P n -> P (S n) -> P (S (S n)))->
    forall n, P n.
Proof.
 intros P H0 H1 Hstep n.
 assert (P n/\P(S n)).
 elim n; intuition.
 intuition.
Qed.

Theorem fib_unroll : 
  forall n, fib (S (S n)) = fib n + fib (S n).
Proof.
 auto.
Qed.

Theorem fib_n_p :
  forall n p, fib (n + p + 2) =
             fib (n + 1) * fib (p + 1) + fib n * fib p. 
Proof.
  intros n; elim n using fib_ind.
  intros p; replace (0 + p+2) with (S (S p)).
  replace (p+1) with (S p).
  rewrite fib_unroll.
  simpl (fib 0).
  simpl (fib (0+1)).
  ring.
  ring.
  ring.

  intros p; replace (1+p+2) with (S (S (S p))).
  repeat rewrite fib_unroll.
  simpl (fib (1+1)).
  simpl (fib 1).
  replace (p+1) with (S p).
  simpl (fib 0).
  ring.
  ring.
  ring.

  intros n' IHn' IHn'1 p.
  replace (S (S n') + p + 2) with (S (S (n'+p + 2))).
  simpl (S (S n') + 1).
  repeat rewrite fib_unroll.
  replace (S (n'+p+2)) with (S n' +p+2).
  rewrite IHn'1.
  rewrite IHn'.
  replace (S n'+1) with (S (S n')).
  replace (S (n'+1)) with (S (S n')).
  rewrite fib_unroll.
  ring.
  ring.
  ring.
  ring.
  ring.
Qed.

Theorem fib_monotonic :  forall n, fib n <= fib (n+1).
Proof.
 intros n; elim n using fib_ind; auto with arith.
 intros n' H1 H2; replace (S (S n')+1) with (S (S (S n'))).
 rewrite (fib_unroll (S n')).
 auto with arith.
 ring.
Qed.

Theorem fib_n_p' :
  forall n p, fib (n + p) =
     fib n * fib p + (fib (n+1) - fib n)*(fib (p+1) - fib p).
Proof.
 intros n; elim n using fib_ind.
 intros p; simpl; ring.

 intros p; replace (1 + p) with (p + 1); simpl.  ring_simplify.
 (*
 ring_simplify. *)
 (*rewrite <- (plus_comm (fib p)).*)
 rewrite le_plus_minus_r.
 auto.
 apply fib_monotonic.
 rewrite plus_comm.
 auto.
 intros n' IHn' IHn'1 p.
 simpl (S (S n') + p).
 rewrite fib_unroll.
 replace (S (n' + p)) with (S n' + p).
 rewrite IHn'.
 rewrite IHn'1.
 simpl (S (S n')+1).
 replace (S n' + 1) with (S (S n')).
 replace (S (n' + 1)) with (S (S n')).
 repeat rewrite fib_unroll.
 rewrite (plus_comm (fib (S n'))
             (fib n' + fib (S n'))).
 rewrite minus_plus.
 rewrite (plus_comm (fib n')(fib (S n'))).
 rewrite minus_plus.
 rewrite mult_minus_distr_r.
 replace
   (fib n' * fib p +
   (fib (n' + 1) * (fib (p + 1) - fib p) - fib n' * (fib (p + 1) - fib p)) +
   (fib (S n') * fib p + fib n' * (fib (p + 1) - fib p)))
  with
   (fib n' * fib p +
   (fib n' * (fib (p + 1) - fib p) +
   (fib (n' + 1) * (fib (p + 1) - fib p) - 
         fib n' * (fib (p + 1) - fib p))) +   fib (S n') * fib p).
 rewrite (le_plus_minus_r).
 replace (n' + 1) with (S n').
 ring.
 ring.
 apply mult_le_compat_r.
 apply fib_monotonic.
 ring.
 ring.
 ring.
 ring.
Qed.

Theorem fib_2n :
  forall n, fib (2*n) = fib (n) * fib (n) + 
           (fib (n+1) - fib n)*(fib (n+1) - fib n).
Proof.
 intros n; replace (2*n) with (n+n).
 apply fib_n_p'.
 ring.
Qed.

Theorem fib_2n_plus_1 :
  forall n, fib (2*n+1) = 2 * fib n * fib (n+1) - fib n * fib n.
Proof.
 intros n; replace (2*n+1) with (n + (n + 1)).
 rewrite fib_n_p'.
 replace (n + 1 + 1) with (S (S n)).
 rewrite fib_unroll.
 replace (S n) with (n + 1).
 rewrite (plus_comm (fib n) (fib (n + 1))).
 rewrite minus_plus.
 apply plus_reg_l with (fib n * fib n).
 rewrite le_plus_minus_r.
 rewrite plus_permute.
 rewrite mult_minus_distr_r.
 rewrite le_plus_minus_r.
 ring.
 apply mult_le_compat_r.
 apply fib_monotonic.
 replace (fib n * fib n) with (1 * (fib n * fib n)).
 rewrite mult_assoc_reverse.
 apply mult_le_compat.
 auto with arith.
 apply mult_le_compat_l.
 apply fib_monotonic.
 ring.
 ring.
 ring.
 ring.
Qed.

Theorem fib_2n_plus_2 :
  forall n, fib (S (2*n+1)) = fib (n+1) * (fib (n+1)) + fib n * fib n.
Proof.
 intros n; replace (S (2*n+1)) with ((n+1)+(n+1)).
 rewrite fib_n_p'.
 replace (n + 1 + 1) with (S (S n)).
 rewrite fib_unroll.
 replace (S n) with (n + 1).
 rewrite (plus_comm (fib n) (fib (n + 1))).
 rewrite minus_plus.
 auto.
 ring.
 ring.
 ring.
Qed.

Theorem th_fib_positive1 :
  forall p : positive,
  forall u v : nat,
    u = fib (nat_of_P p) /\ v = fib (S (nat_of_P p)) ->
      2*u*v - u*u = fib(nat_of_P (xI p)) /\
      v*v + u*u = fib(S (nat_of_P (xI p))).
Proof.
 intros p u v [Hu Hv]; rewrite Hu; rewrite Hv.
 rewrite nat_of_P_xI.
 replace (S (2* nat_of_P p)) with (2*nat_of_P p + 1).
 rewrite fib_2n_plus_1.
 rewrite fib_2n_plus_2.
 replace (S (nat_of_P p)) with (nat_of_P p + 1).
 auto.
 ring.
 ring.
Qed.
          
Theorem th_fib_positive0 :
  forall p : positive,
  forall u v : nat,
    u = fib (nat_of_P p) /\ v = fib (S (nat_of_P p)) ->
    u*u + (v-u)*(v-u) = fib (nat_of_P (xO p)) /\
    2*u*v - u*u = fib (S (nat_of_P (xO p))).
Proof.
 intros p u v [Hu Hv]; subst.
 rewrite nat_of_P_xO.
 rewrite fib_2n.
 replace (S (nat_of_P p)) with (nat_of_P p + 1).
 replace (S (2*nat_of_P p)) with (2*nat_of_P p+1).
 rewrite fib_2n_plus_1.
 auto.
 ring.
 ring.
Qed.

Fixpoint fib_positive (p:positive) :
  {u:nat & { v : nat | u = fib (nat_of_P p) /\  v = fib (S (nat_of_P p))}} :=
match p return 
   {u:nat & { v : nat | u = fib (nat_of_P p) /\  v = fib (S (nat_of_P p))}}
     with
  xH => (existS (fun u=> { v : nat | u = 1 /\  v = 2})
              1 (exist (fun v => 1 = 1 /\  v = 2)
                    2 (conj (refl_equal 1) (refl_equal 2))))
| xI p' =>
   match fib_positive p' with
     (existS _ u (exist _ v h)) =>
       (existS (fun u =>
                  { v: nat | u = fib (nat_of_P (xI p')) /\
                             v = fib (S (nat_of_P (xI p')))})
           (2*u*v - u*u)
          (exist (fun w=> 2*u*v-u*u = fib (nat_of_P (xI p')) /\
                            w= fib (S (nat_of_P (xI p'))))
             (v*v + u*u) (th_fib_positive1 p' u v h)))
   end
| xO p' =>
   match fib_positive p' with
     (existS _ u (exist _ v h)) =>
       (existS (fun u =>
                  { v: nat | u = fib (nat_of_P (xO p')) /\
                             v = fib (S (nat_of_P (xO p')))})
            (u*u+(v-u)*(v-u))
          (exist (fun w => u*u+(v-u)*(v-u) = fib (nat_of_P (xO p'))/\
                           w = fib (S (nat_of_P (xO p'))))
                (2*u*v-u*u) (th_fib_positive0 p' u v h)))
   end
end.

Definition fib' :
  forall n:nat, {u : nat &{v : nat | u = fib n /\ v = fib (S n)}}.
Proof.
  intros n; case n.
  exists 1; exists 1; auto.
  intros n'; elim (fib_positive (P_of_succ_nat n'));
  intros u [v [Hu Hv]].
  exists u; exists v.
  rewrite Hu; rewrite Hv; rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
  auto.
Qed.
