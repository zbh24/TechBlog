Require Import Arith.
Require Import List.

Fixpoint nth_option' (A:Set)(n:nat)(l:list A){struct n}
  : option A :=
  match n, l with
  | O, cons a tl => Some a
  | S p, cons a tl => nth_option' A p tl
  | n, nil => None
  end.

Fixpoint nth_option (A:Set)(n:nat)(l:list A){struct l}
  : option A :=
  match n, l with
  | O, cons a tl => Some a
  | S p, cons a tl => nth_option A p tl
  | n, nil => None
  end.


Goal forall (A:Set) (n:nat) (l:list A),
  nth_option A n l = nth_option' A n l.
induction n; induction l; simpl; auto.
Qed.

