Require Import ProofObjects.
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



Require Import ProofObjects.
Import Check.

Goal True.
idtac "Entering exercise eight_is_even (standard): 1 point".
idtac " ".

idtac "#> ev_8".
check_type @ev_8 (ev 8).
idtac "Assumptions:".
Abort.
Print Assumptions ev_8.
Goal True.
idtac " ".

idtac "#> ev_8'".
check_type @ev_8' (ev 8).
idtac "Assumptions:".
Abort.
Print Assumptions ev_8'.
Goal True.
idtac " ".

idtac "Exiting exercise (eight_is_even)".
idtac " ".

idtac "Entering exercise leibniz_equality (standard): 2 points".
idtac " ".

idtac "#> MyEquality.leibniz_equality".
check_type @MyEquality.leibniz_equality (forall (X : Type) (x y: X),  x = y -> forall P:X->Prop, P x -> P y).
idtac "Assumptions:".
Abort.
Print Assumptions MyEquality.leibniz_equality.
Goal True.
idtac " ".

idtac "Exiting exercise (leibniz_equality)".
idtac " ".

idtac "Max points - regular: 3".
idtac "Max points - advanced: 3".
Abort.
