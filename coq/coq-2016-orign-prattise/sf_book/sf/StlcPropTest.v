Require Import StlcProp.
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



Require Import StlcProp.
Import Check.

Goal True.
idtac "Entering exercise afi (standard): 1 point".
idtac " ".

idtac "Exiting exercise (afi)".
idtac " ".

idtac "Entering exercise subject_expansion_stlc (standard): 2 points".
idtac " ".

idtac "#> STLCProp.soundness".
check_type @STLCProp.soundness (forall t t' T,  empty |- t \in T ->  t ==>* t' ->  ~(stuck t')).
idtac "Assumptions:".
Abort.
Print Assumptions STLCProp.soundness.
Goal True.
idtac " ".

idtac "Exiting exercise (subject_expansion_stlc)".
idtac " ".

idtac "Entering exercise types_unique (standard): 3 points".
idtac " ".

idtac "Exiting exercise (types_unique)".
idtac " ".

idtac "Entering exercise progress_preservation_statement (standard): 1 point".
idtac " ".

idtac "Exiting exercise (progress_preservation_statement)".
idtac " ".

idtac "Entering exercise stlc_variation1 (standard): 2 points".
idtac " ".

idtac "Entering exercise stlc_variation2 (standard): 2 points".
idtac " ".

idtac "Entering exercise stlc_variation3 (standard): 2 points".
idtac " ".

idtac "Entering exercise stlc_arith (standard): 4 points".
idtac " ".

idtac "Exiting exercise (stlc_arith)".
idtac " ".

idtac "Max points - regular: 17".
idtac "Max points - advanced: 17".
Abort.
