Definition dyslexic_imp := forall P Q:Prop, (P -> Q) -> Q -> P.

Definition dyslexic_contrap := forall P Q:Prop, (P -> Q) -> ~ P -> ~ Q.


Section dyslexia.
 Hypothesis d : dyslexic_imp.

 Theorem incons1 : False. 
 Proof.
  apply d with True; trivial.
 Qed.

End dyslexia.

Section dyslexia2.
 Hypothesis s : dyslexic_contrap.

 Lemma incons2 : False.
 Proof.
  apply s with False True; try trivial.
  red; trivial.
 Qed.

End dyslexia2.
