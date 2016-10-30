Section on_ex. 
  Variables 
   (A:Type)
   (P Q:A -> Prop).

 Lemma ex_or : (exists x:A, P x \/ Q x) -> ex P \/ ex Q.
 Proof.
  intro H; elim H; intros x [H1|H1].
  left ; exists x; trivial.
  right ; exists x; trivial.
 Qed.
 
 Lemma ex_or_R : ex P \/ ex Q -> (exists x:A, P x \/ Q x).
 Proof.
  intros [H | H]; case H; intros x Hx; exists x; auto.
 Qed.

 Lemma two_is_three : (exists x:A, forall R : A->Prop, R x) -> 2 = 3.
 Proof.
  intro H; elim H; intros x Hx.
  elim (Hx (fun y:A => False)).
 Qed.

 Lemma forall_no_ex : (forall x:A, P x) -> ~(exists y:A, ~ P y).
 Proof.
  intros H H0; elim H0.
  intros x Hx; apply Hx ; apply H.
 Qed.

End on_ex.
