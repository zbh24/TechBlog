Require Import Relations.

Lemma wf_inclusion :
 forall (A:Set) (R S:A -> A -> Prop),
   inclusion A R S -> well_founded S -> well_founded R.
Proof.
 intros A R S Hincl Hwf x.
 elim x using (well_founded_ind Hwf).
 intros x' Hrec; apply Acc_intro.
 intros y Hr; apply Hrec; apply Hincl; assumption.
Qed.