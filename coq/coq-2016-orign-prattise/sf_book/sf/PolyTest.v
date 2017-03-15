Require Import Poly.
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



Require Import Poly.
Import Check.

Goal True.
idtac "Entering exercise split (standard): 2 points".
idtac " ".

idtac "#> split".
check_type @split (forall (X Y :  Type), forall (l :  list (X*Y)),  (list X) * (list Y)).
idtac "Assumptions:".
Abort.
Print Assumptions split.
Goal True.
idtac " ".

idtac "#> test_split".
check_type @test_split (split [(1,false);(2,false)] = ([1;2],[false;false])).
idtac "Assumptions:".
Abort.
Print Assumptions test_split.
Goal True.
idtac " ".

idtac "Exiting exercise (split)".
idtac " ".

idtac "Entering exercise filter_even_gt7 (standard): 2 points".
idtac " ".

idtac "#> filter_even_gt7".
check_type @filter_even_gt7 (forall (l :  list nat),  list nat).
idtac "Assumptions:".
Abort.
Print Assumptions filter_even_gt7.
Goal True.
idtac " ".

idtac "#> test_filter_even_gt7_1".
check_type @test_filter_even_gt7_1 (filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8]).
idtac "Assumptions:".
Abort.
Print Assumptions test_filter_even_gt7_1.
Goal True.
idtac " ".

idtac "#> test_filter_even_gt7_2".
check_type @test_filter_even_gt7_2 (filter_even_gt7 [5;2;6;19;129] = []).
idtac "Assumptions:".
Abort.
Print Assumptions test_filter_even_gt7_2.
Goal True.
idtac " ".

idtac "Exiting exercise (filter_even_gt7)".
idtac " ".

idtac "Entering exercise partition (standard): 3 points".
idtac " ".

idtac "#> partition".
check_type @partition (forall (X :  Type), forall (test :  X -> bool), forall (l :  list X),  list X * list X).
idtac "Assumptions:".
Abort.
Print Assumptions partition.
Goal True.
idtac " ".

idtac "#> test_partition1".
check_type @test_partition1 (partition oddb [1;2;3;4;5] = ([1;3;5], [2;4])).
idtac "Assumptions:".
Abort.
Print Assumptions test_partition1.
Goal True.
idtac " ".

idtac "#> test_partition2".
check_type @test_partition2 (partition (fun x => false) [5;9;0] = ([], [5;9;0])).
idtac "Assumptions:".
Abort.
Print Assumptions test_partition2.
Goal True.
idtac " ".

idtac "Exiting exercise (partition)".
idtac " ".

idtac "Entering exercise map_rev (standard): 3 points".
idtac " ".

idtac "#> map_rev".
check_type @map_rev (forall (X Y : Type) (f : X -> Y) (l : list X),  map f (rev l) = rev (map f l)).
idtac "Assumptions:".
Abort.
Print Assumptions map_rev.
Goal True.
idtac " ".

idtac "Exiting exercise (map_rev)".
idtac " ".

idtac "Entering exercise flat_map (standard): 2 points".
idtac " ".

idtac "#> flat_map".
check_type @flat_map (forall (X Y : Type), forall (f : X -> list Y), forall (l : list X),  (list Y)).
idtac "Assumptions:".
Abort.
Print Assumptions flat_map.
Goal True.
idtac " ".

idtac "#> test_flat_map1".
check_type @test_flat_map1 (flat_map (fun n => [n;n;n]) [1;5;4]  = [1; 1; 1; 5; 5; 5; 4; 4; 4]).
idtac "Assumptions:".
Abort.
Print Assumptions test_flat_map1.
Goal True.
idtac " ".

idtac "Exiting exercise (flat_map)".
idtac " ".

idtac "Entering exercise fold_types_different (advanced): 1 point".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (fold_types_different)".
idtac " ".

idtac "Max points - regular: 12".
idtac "Max points - advanced: 13".
Abort.
