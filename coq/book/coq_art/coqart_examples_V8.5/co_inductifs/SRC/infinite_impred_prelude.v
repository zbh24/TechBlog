
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


