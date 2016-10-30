Require Import Coinduc.

Section counter_example.
 Let A : Set := nat.
 Let P l := match l with (LCons 0 l') => True 
                        | other       => False
                    end.
 Let u := omega_repeat 1.
 Let v := LCons 0 LNil.

 
 Lemma L1 : satisfies v (Eventually P).
 Proof.
  unfold v, P;  left ; trivial.
 Qed.

 Lemma L2 : u = (LCons 1 u).
 Proof.
  unfold u; apply omega_repeat_unfold.
 Qed.

 Lemma L3 : forall (w: LList nat), satisfies w (Eventually P) -> 
                                   exists n : nat, LNth n w = Some 0.
 Proof.
  induction 1.
  generalize H; case a;  simpl in H.
  exists 0.
  simpl.
  trivial.
  simpl.
  contradiction.
  case IHEventually; intros p Hp.
  exists (S p);simpl; auto.
 Qed.
 
 Lemma L4 : (bisimilar u (LAppend u v)).
 Proof.
   apply LAppend_of_Infinite_eq.
    unfold u;  apply omega_repeat_infinite.
 Qed.
 
 Lemma L5 : forall n, LNth n u = Some 1.
 Proof.
  simple induction n.
  rewrite L2.
  simpl.
  trivial.
  intros n0 H0; rewrite L2; simpl; auto.
 Qed.
 
 Lemma L6 : forall n, LNth n (LAppend u v) = Some 1.
 Proof.
  intro n;  transitivity (LNth n u).
   apply bisimilar_LNth.
   generalize (bisimilar_sym (A:=nat)).
   Import Relations.
   unfold symmetric.
   intro H;apply H.
   apply L4.
   apply L5.
 Qed.


 Lemma L7 : ~(satisfies (LAppend u v) (Eventually P)).
 Proof.
  intro H.
  case (L3  _ H).
  intros n  H1.
  generalize (L6 n).
  rewrite  H1.
  discriminate 1.
 Qed.

End counter_example.  

