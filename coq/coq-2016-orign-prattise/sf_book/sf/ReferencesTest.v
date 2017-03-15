Require Import References.
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



Require Import References.
Import Check.

Goal True.
idtac "Entering exercise store_draw (standard): 1 point".
idtac " ".

idtac "Exiting exercise (store_draw)".
idtac " ".

idtac "Entering exercise compact_update (standard): 2 points".
idtac " ".

idtac "Exiting exercise (compact_update)".
idtac " ".

idtac "Entering exercise type_safety_violation (standard): 1 point".
idtac " ".

idtac "Exiting exercise (type_safety_violation)".
idtac " ".

idtac "Entering exercise cyclic_store (standard): 2 points".
idtac " ".

idtac "Exiting exercise (cyclic_store)".
idtac " ".

idtac "Entering exercise store_not_unique (standard): 2 points".
idtac " ".

idtac "Exiting exercise (store_not_unique)".
idtac " ".

idtac "Entering exercise preservation_informal (standard): 3 points".
idtac " ".

idtac "Entering exercise factorial_ref (standard): 4 points".
idtac " ".

idtac "#> STLCRef.RefsAndNontermination.factorial".
check_type @STLCRef.RefsAndNontermination.factorial (tm).
idtac "Assumptions:".
Abort.
Print Assumptions STLCRef.RefsAndNontermination.factorial.
Goal True.
idtac " ".

idtac "#> STLCRef.RefsAndNontermination.factorial_type".
check_type @STLCRef.RefsAndNontermination.factorial_type (empty; nil |- factorial \in (TArrow TNat TNat)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCRef.RefsAndNontermination.factorial_type.
Goal True.
idtac " ".

idtac "Exiting exercise (factorial_ref)".
idtac " ".

idtac "Max points - regular: 15".
idtac "Max points - advanced: 15".
Abort.
