Set Implicit Arguments.


CoInductive LList (A:Set) : Set :=
  | LNil : LList A
  | LCons : A -> LList A -> LList A.

Implicit Arguments LNil [A].

CoInductive Infinite (A:Set) : LList A -> Prop :=
    Infinite_LCons :
      forall (a:A) (l:LList A), Infinite l -> Infinite (LCons a l).


Hint Resolve Infinite_LCons: llists.

  

Definition Infinite_ok (A:Set) (X:LList A -> Prop) :=
  forall l:LList A,
    X l ->  exists a : A, exists l' : LList A, l = LCons a l' /\ X l'.
 
Definition Infinite1 (A:Set) (l:LList A) :=
   exists X : LList A -> Prop, Infinite_ok X /\ X l.


Lemma ok_LNil :
 forall (A:Set) (X:LList A -> Prop), Infinite_ok X -> ~ X LNil.
Proof.
 intros.
 unfold not in |- *; intro.
 case (H LNil).
 auto.
 intros x H1; case H1; intros x0 H2.
 case H2; discriminate 1.
Qed.

Lemma ok_LCons :
 forall (A:Set) (X:LList A -> Prop) (a:A) (l:LList A),
   Infinite_ok X -> X (LCons a l) -> X l.
Proof.
 intros A X a l H H0.
 case (H (LCons a l)).
 assumption.
 simple destruct 1.
 intros x0 H2; case H2; injection 1.
 simple destruct 1; auto.
Qed.



Lemma Infinite1_LNil : forall A:Set, ~ Infinite1 (LNil (A:=A)).
Proof.
 unfold not in |- *; intros A H.
 case H; intros X HX.
 case HX; intros H1 H2.
 apply (ok_LNil H1).
 auto.
Qed.


Lemma Infinite1_LCons :
 forall (A:Set) (a:A) (l:LList A), Infinite1 (LCons a l) -> Infinite1 l.
Proof.
 intros A a l H.
 case H; intros X HX; case HX; intros H1 H2; clear HX.
 exists (fun u:LList A =>  exists b : A, X (LCons b u)).
 split.
 unfold Infinite_ok in |- *.
 simple destruct 1; intros.
 cut (X l0).
 intro H4.
 case (H1 l0 H4).
 intros.
 case H5; intros l' Hl'.
 case Hl'; intros e' H'.
 exists x0.
 exists l'.
 split; try assumption.
 exists x0; case e'; auto.
 eapply ok_LCons.
 assumption.
 eexact H3.
 exists a; auto.
Qed.

(* equivalence between both definitions of infinity *)


Lemma Inf_Inf1 : forall (A:Set) (l:LList A), Infinite l -> Infinite1 l.
Proof.
 intros.
 exists (Infinite (A:=A)).
 split; try assumption.
 unfold Infinite_ok in |- *.
 simple destruct l0.
 inversion 1.
 inversion_clear 1.
 exists a; exists l1; auto.
Qed.

Lemma Inf1_Inf : forall (A:Set) (l:LList A), Infinite1 l -> Infinite l.
Proof.
 cofix.
 simple destruct l.
 intro H.
 case (Infinite1_LNil H).
 intros.
 generalize (Infinite1_LCons H).
 intro; constructor.
 Guarded.
 auto.
Qed.

