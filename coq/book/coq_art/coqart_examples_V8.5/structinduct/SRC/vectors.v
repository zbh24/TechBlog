Require Import Vector.


Fixpoint vector_nth (A:Set)(n:nat)(p:nat)(v:t A p){struct v}
                  : option A :=
  match n,v  with
    _   , nil _ => None
  | 0   , cons _ b  _ _ => Some b
  | S n', cons _ _  p' v' => vector_nth A n'  p' v'
  end.

(* examples *)

Implicit Arguments cons [A n].
Implicit Arguments nil [A].

Definition v0 := cons true  (cons false  (cons false  nil)).

Implicit Arguments vector_nth [A p].

Eval compute in vector_nth 2 v0 .
Eval compute in vector_nth 1 v0.
Eval compute in vector_nth 0 v0.
Eval compute in vector_nth 10 v0 .

Theorem nth_size : forall (A:Set)(p:nat)(v:t A p)(n:nat), 
  vector_nth n v  = None <-> p <= n.
Proof.
 induction v;simpl; auto. 
 intro n; case n; simpl; split; auto with arith. 
 intro n0;case n0;simpl;split.
 discriminate 1.
 inversion 1.
 case (IHv n1);auto with arith.
 case (IHv n1);auto with arith.
Qed.




 


 
