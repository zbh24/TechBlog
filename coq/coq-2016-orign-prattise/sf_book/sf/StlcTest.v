Require Import Stlc.
Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
match type of A with
| context[MISSING] => idtac "Missing:" A
| ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be " B]
end.

Ltac check_exists A :=
match type of A with
| context[MISSING] => idtac "Missing:" A
| ?T => idtac "Is present."; idtac "Check type:" T
end.
End Check.



Require Import Stlc.
Import Check.

Goal True.
idtac "Entering exercise substi (standard): 3 points".
idtac " ".

idtac "#> STLC.substi_correct".
check_type @STLC.substi_correct (forall s x t t',  [x).
idtac "Assumptions:".
Abort.
Print Assumptions STLC.substi_correct.
Goal True.
idtac " ".

idtac "Exiting exercise (substi)".
idtac " ".

idtac "Max points - regular: 3".
idtac "Max points - advanced: 3".
Abort.
