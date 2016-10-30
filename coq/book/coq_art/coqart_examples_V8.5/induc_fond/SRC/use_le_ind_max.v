 
Definition pred_partial: forall (n : nat), n <> 0 ->  nat.
intros n; case n.
intros h; elim h; reflexivity.
intros p h'; exact p.
Defined.
 
Scheme
le_ind_max := Induction for le Sort Prop.
 
Theorem le_2_n_not_zero: forall (n : nat), 2 <= n ->  (n <> 0).
Proof.
intros n Hle; elim Hle; intros; discriminate.
Qed.
 
Theorem le_2_n_pred:
 forall (n : nat) (h : 2 <= n),  (pred_partial n (le_2_n_not_zero n h) <> 0).
Proof.
 intros n h; elim h  using le_ind_max.
 simpl.
 auto.
 intros m h' IHh'.
 simpl.
 inversion h'; auto.
Qed.
