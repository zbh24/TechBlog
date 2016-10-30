Require Import Classical.

Axiom functional_choice : forall (A:Set)(S:A->A->Prop), 
                      (forall x, exists y, S x y )-> 
                          exists f, forall x, S x (f x).


Section nowf.

 Variables (A:Set)(R: A -> A -> Prop).

 Hypothesis R_not_wf : not (well_founded R).

 Remark  ex_not_acc :  exists x:A, ~ (Acc R x).
 Proof.
  apply not_all_ex_not;auto.
 Qed.
 
 
 Lemma go_down : forall x, ~ Acc R x -> exists y, R y x /\ ~ Acc R y.
 Proof.
 intros.
 change (exists z, (fun y => R y x /\ ~ Acc R y) z).
 apply not_all_not_ex.
 intro.
 assert (forall n, R n x -> Acc R n).
 intros.
 generalize (H0 n).
 intro.
 case (not_and_or _ _ H2).
 destruct 1;auto.
 intros;apply NNPP;auto. 
 apply H.
 split;auto.
 Qed.


 Lemma decrease : exists f, 
       forall x, ~ Acc R x ->  ~ Acc R (f x) /\ R (f x) x.
 Proof.
 case (functional_choice A (fun x y =>  Acc R x \/ R y x /\ ~ Acc R y)).
 intros.
 case (classic (Acc R x)).
 exists x;auto.
 intros.
 case (go_down _ H).
 intros;exists x0.
 tauto.
 intros.
 exists x.
 intros.
 case (H x0).
 tauto.
 tauto.
Qed.

Theorem ok : exists f : nat -> A, forall n, R (f (S n)) (f n). 
Proof.
  case decrease.
  intros f Hf.
  case ex_not_acc;intros z0 Hz.
   pose (F := (fix F (n:nat) : A := 
                  match n with
                          | 0 => z0 
                          | S p => f (F p) 
                  end)).
  exists F.
 assert (forall n, R (F (S n)) (F n) /\ ~ Acc R (F n) /\ ~ Acc R (F (S n))).
 induction n.
 unfold F;
 case (Hf z0 Hz).
 tauto.
 decompose [and] IHn. 
 split;auto.
 simpl.
 simpl in H2.
 case (Hf _ H2).
 auto.
 split;auto.
 case (Hf _ H2).
 simpl;auto.
 simpl.
 intros.
 case (H n).
 simpl;tauto.
Qed.

End nowf.

Check ok.




 
 
