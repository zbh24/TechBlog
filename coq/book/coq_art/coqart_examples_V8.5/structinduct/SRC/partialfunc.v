Section partial_functions.

 Variable P : nat -> Prop.
 Variable f : nat -> option nat.
 
 Hypothesis f_domain : forall n, P n <-> f n <> None.

 Definition g n : option nat := 
     match f (n+2) with None => None 
                      | Some y => Some (y + 2) end.


 Lemma g_domain : forall n, P (n+2) <-> g n <> None.
 unfold g; intro n; case (f_domain (n+2)); intros H1 H2.
 split.
 intros.
 case_eq (f (n+2)).  
 intros;discriminate.
 intro ;case (H1 H);assumption. 
 case_eq (f (n+2)); simpl.
 intros n0 Hn0 diff.
 apply H2; rewrite Hn0.
 discriminate.
 destruct 2;auto.
Qed.
 
End partial_functions.
