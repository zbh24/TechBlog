Definition sig_rec_simple (A:Set) (P: A -> Prop) (B : Set) :
  (forall x, P x -> B) -> (sig P) -> B.
 intros   f x.
 case x; intros a Ha.
 eapply f ; eexact Ha. 
Defined.




