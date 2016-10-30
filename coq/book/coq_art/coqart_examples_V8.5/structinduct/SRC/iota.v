Require Import Arith.
Require Import List.

Definition iota (n:nat) : list nat :=
  (fix f (p:nat)(l:(list nat)){struct p}:list nat :=
       match p with
       | 0 => l 
       | S q => f q ((S q)::l) 
       end) 
   n nil.

Eval compute in (iota 7).

