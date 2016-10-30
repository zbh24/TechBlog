Lemma and_assoc : forall A B C:Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
 intros A B C [a [b c]]; repeat split; assumption.
Qed.


Lemma and_imp_dist : forall A B C D:Prop,
   (A -> B) /\ (C -> D) -> A /\ C -> B /\ D.
Proof.
  intros A B C D [H1 H2] [a c].
  split;[apply H1|apply H2];assumption.
Qed.


Lemma not_contrad : forall A : Prop, ~(A /\ ~A).
Proof.
 intros A [a a']; apply a'; assumption.
Qed.

Lemma or_and_not : forall A B : Prop, (A\/B)/\~A -> B.
Proof.
 intros A B [[a|b] a'];[elim a'| idtac]; trivial.
Qed.


