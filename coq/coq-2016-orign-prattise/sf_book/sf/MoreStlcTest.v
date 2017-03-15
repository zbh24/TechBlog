Require Import MoreStlc.
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



Require Import MoreStlc.
Import Check.

Goal True.
idtac "Entering exercise STLC_extensions (standard): 4 points".
idtac " ".

idtac "Exiting exercise (STLC_extensions)".
idtac " ".

idtac "Max points - regular: 4".
idtac "Max points - advanced: 4".
Abort.
