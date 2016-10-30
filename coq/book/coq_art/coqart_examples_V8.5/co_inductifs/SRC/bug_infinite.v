Require Import Arith.
Set Implicit Arguments.

CoInductive LList (A:Set) : Set :=
  | LNil : LList A
  | LCons : A -> LList A -> LList A.

Implicit Arguments LNil [A].

Inductive BugInfinite (A:Set) : LList A -> Prop :=
    BugInfinite_intro :
      forall a (l:LList A),
        BugInfinite l -> BugInfinite (LCons a l).      

Theorem bug_infinite_empty :
  forall (A:Set) (l:LList A), BugInfinite l -> False.
Proof.
  induction 1.
  auto.
Qed.

