Require Import Sub.
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



Require Import Sub.
Import Check.

Goal True.
idtac "Entering exercise arrow_sub_wrong (standard): 2 points".
idtac " ".

idtac "Entering exercise subtype_order (standard): 2 points".
idtac " ".

idtac "Entering exercise subtype_instances_tf_2 (standard): 1 point".
idtac " ".

idtac "Entering exercise subtype_concepts_tf (standard): 1 point".
idtac " ".

idtac "Entering exercise proper_subtypes (standard): 2 points".
idtac " ".

idtac "Entering exercise small_large_1 (standard): 2 points".
idtac " ".

idtac "Entering exercise small_large_2 (standard): 2 points".
idtac " ".

idtac "Entering exercise small_large_4 (standard): 2 points".
idtac " ".

idtac "Entering exercise smallest_1 (standard): 2 points".
idtac " ".

idtac "Entering exercise smallest_2 (standard): 2 points".
idtac " ".

idtac "Entering exercise pair_permutation (standard): 2 points".
idtac " ".

idtac "#> Examples.Person".
check_type @Examples.Person (ty).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.Person.
Goal True.
idtac " ".

idtac "#> Examples.Student".
check_type @Examples.Student (ty).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.Student.
Goal True.
idtac " ".

idtac "#> Examples.Employee".
check_type @Examples.Employee (ty).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.Employee.
Goal True.
idtac " ".

idtac "#> Examples.sub_student_person".
check_type @Examples.sub_student_person (Student <: Person).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.sub_student_person.
Goal True.
idtac " ".

idtac "#> Examples.sub_employee_person".
check_type @Examples.sub_employee_person (Employee <: Person).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.sub_employee_person.
Goal True.
idtac " ".

idtac "Exiting exercise (pair_permutation)".
idtac " ".

idtac "Entering exercise variations (standard): 2 points".
idtac " ".

idtac "Entering exercise products (standard): 4 points".
idtac " ".

idtac "Max points - regular: 26".
idtac "Max points - advanced: 26".
Abort.
