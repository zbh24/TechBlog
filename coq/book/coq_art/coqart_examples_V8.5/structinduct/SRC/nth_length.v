Require Import List.
Require Import Arith.

Fixpoint nth_option (A:Set)(n:nat)(l:list A) {struct l}
  : option A :=
  match n, l with
  | O, cons a tl =>  Some a
  | S p, cons a tl => nth_option A p tl
  | n, nil => None
  end.

Lemma nth_length : 
  forall (A:Set)(n:nat)(l:list A), nth_option _ n l = None <->
                                   length l <= n.
Proof.
 simple induction n.
 destruct l; simpl; split; auto.
 discriminate 1.
 inversion 1.
 intros n0 Hn0 l; destruct l;
  split;simpl; auto with arith.
 case (Hn0 l);auto with arith.
 case (Hn0 l);auto with arith.
Qed.

 
