
Section Minimal_propositional_logic.
 Variables P Q R T : Prop.

 Check ((P->Q)->(Q->R)->P->R).

 Theorem imp_trans : (P->Q)->(Q->R)->P->R.
 Proof.
  intros H H' p.
  apply H'.
  apply H.
  assumption.
 Qed.

 Print imp_trans.
 
 Theorem imp_trans' : (P->Q)->(Q->R)->P->R.
 Proof.
  auto.
 Qed.
 
 Theorem delta : (P->P->Q)->P->Q.
 Proof (fun (H:P->P->Q)(p:P) => H p p).

 Lemma apply_example : (Q->R->T)->(P->Q)->P->R->T.
 Proof.
  intros H H0 p.
  apply H.
  exact (H0 p).
 Qed.

 Theorem imp_dist : (P->Q->R)->(P->Q)->(P->R).
 Proof.
  intros H H' p.
  apply H.
  assumption.
  apply H'.
  assumption.
 Qed.

 Print imp_dist.

 Theorem K : P->Q->P.
 Proof.
  intros p q.
  assumption.
 Qed.


 Definition f : (nat->bool)->(nat->bool)->nat->bool.
  intros f1 f2.
  assumption.
 Defined.

 Print f.

 Eval compute in (f (fun n => true)(fun n => false) 45).

 Opaque f.

 Eval compute in (f (fun n => true)(fun n => false) 45).

 Section proof_of_triple_impl.
  Hypothesis H : ((P->Q)->Q)-> Q.
  Hypothesis p : P.

  Lemma Rem : (P->Q)->Q.
  Proof (fun H0:P->Q => H0 p).

  Theorem triple_impl : Q.
  Proof (H Rem).

 End proof_of_triple_impl.

 Print triple_impl.

 Print Rem.

 Lemma then_example : P->Q->(P->Q->R)->R.
 Proof.
  intros p q H.
  apply H; assumption.
 Qed.

 Theorem triple_impl_one_shot : (((P->Q)->Q)->Q)->P->Q.
 Proof.
  intros H p; apply H; intro H0; apply H0; assumption.
 Qed.

 Lemma compose_example : (P->Q->R)->(P->Q)->(P->R).
 Proof.
  intros H H' p.
  apply H;[assumption | apply H'; assumption].
 Qed.

 Theorem orelse_example : (P->Q)->R->((P->Q)->R->(T->Q)->T)->T.
 Proof.
  intros H r H0.
  apply H0;(assumption || intro H1).
  Abort.
  
 Lemma L3 : (P->Q)->(P->R)->(P->Q->R->T)->P->T.
 Proof.
  intros H H0 H1 p.
  apply H1;[idtac | apply H | apply H0]; assumption.
 Qed.

 Lemma then_fail_example : (P->Q)->(P->Q).
 Proof.
  intro X; apply X; fail.
 Qed.

 Lemma try_example : (P->Q->R->T)->(P->Q)->(P->R->T).
 Proof.
  intros H H' p r.
  apply H; try assumption.
  apply H'; assumption.
 Qed.
 Reset imp_dist.

 Theorem imp_dist : (P->Q->R)->(P->Q)->(P->R).
 Proof.
  intros.
  apply H.
  assumption.
  apply H0.
  assumption.
 Qed.

 Section proof_cut_and_paste.
  Hypothesis H : ((P->Q)->Q)->(P->Q)->R.

  Theorem  imp_dist_2 : (P->Q->R)->(P->Q)->(P->R) .
  Proof (* copy of imp_dist proof script *).
   intros.
   apply H.
  Abort.
  End proof_cut_and_paste.

 Section section_for_cut_example.
  Hypotheses (H : P->Q)
             (H0 : Q->R)
             (H1 : (P->R)->T->Q)
             (H2 : (P->R)->T).
 
  Lemma cut_example : Q.
  Proof.
   cut (P->R).
   intro H3.
   apply H1;[assumption | apply H2; assumption].
   intro; apply H0; apply H; assumption.
  Qed.
 Print cut_example.
 End section_for_cut_example.

 Lemma triple_impl2 : (((P->Q)->Q)->Q)->P->Q.
 Proof.
  auto.
 Qed.

End Minimal_propositional_logic.

Print imp_dist.

Section using_imp_dist.
 Variables (P1 P2 P3 : Prop).
 Check (imp_dist P1 P2 P3).

 Check (imp_dist (P1->P2)(P2->P3)(P3->P1)).

End using_imp_dist.

