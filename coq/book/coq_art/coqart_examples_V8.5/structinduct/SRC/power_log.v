Require Import ZArith.

Open Scope Z_scope.

Fixpoint power (z:Z)(n:nat) {struct n} : Z :=
 match n with 
 | 0%nat => 1
 | S p => z * (power z p)
 end.
          

Eval compute in (power (-2) 10).

Open Scope nat_scope.

Fixpoint discrete_log (p:positive) : nat :=
  match p with 
   | xH => 0
   | xI q => S (discrete_log q)
   | xO q => S (discrete_log q)
 end.
   
Eval compute in (discrete_log 127%positive).
Eval compute in (discrete_log 128%positive).
Eval compute in (discrete_log 255%positive).
