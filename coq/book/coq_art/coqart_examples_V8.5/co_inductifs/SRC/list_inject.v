Set Implicit Arguments.

Require Import List.
Require Import Image.

CoInductive LList (A:Set) : Set :=
  | LNil : LList A
  | LCons : A -> LList A -> LList A.

Implicit Arguments LNil [A].

Fixpoint llist_injection (A:Set) (l:list A) {struct l} : 
 LList A :=
  match l with
  | nil => LNil
  | a :: l' => LCons a (llist_injection l')
  end.

Theorem llist_injection_inj :
 forall A:Set, injective _ _ (llist_injection (A:=A)).
Proof.
 unfold injective in |- *; intro A.
 simple induction x; simpl in |- *.
 simple destruct y; simpl in |- *; [ auto | discriminate 1 ].
 intros a l Hl y; case y; simpl in |- *.
 discriminate 1.
 injection 1; intros e1 e2; rewrite e2; rewrite (Hl _ e1); trivial.
Qed.
