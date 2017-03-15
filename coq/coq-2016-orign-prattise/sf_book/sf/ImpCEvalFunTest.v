Require Import ImpCEvalFun.
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



Require Import ImpCEvalFun.
Import Check.

Goal True.
idtac "Entering exercise pup_to_n (standard): 2 points".
idtac " ".

idtac "#> pup_to_n".
check_type @pup_to_n (com).
idtac "Assumptions:".
Abort.
Print Assumptions pup_to_n.
Goal True.
idtac " ".

idtac "Exiting exercise (pup_to_n)".
idtac " ".

idtac "Entering exercise ceval_step__ceval_inf (standard): 4 points".
idtac " ".

idtac "Entering exercise ceval__ceval_step (standard): 3 points".
idtac " ".

idtac "#> ceval__ceval_step".
check_type @ceval__ceval_step (forall c st st',      c / st \\ st' ->      exists i, ceval_step st c i = Some st').
idtac "Assumptions:".
Abort.
Print Assumptions ceval__ceval_step.
Goal True.
idtac " ".

idtac "Exiting exercise (ceval__ceval_step)".
idtac " ".

idtac "Max points - regular: 9".
idtac "Max points - advanced: 9".
Abort.
