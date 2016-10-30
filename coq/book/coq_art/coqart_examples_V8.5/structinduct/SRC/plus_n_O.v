Open Scope nat_scope.

Theorem plus_n_O : forall n, n+0 =n.
Proof.
 intro n; elim n; simpl.
 reflexivity.
 intros n0 e.
 apply eq_ind with (P:= fun n => S(n0 + 0) = S n) (x:= n0 + 0). 
 reflexivity.
 assumption.
Qed.

