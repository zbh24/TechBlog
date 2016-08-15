Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

Definition test1(n:nat) := 3.

Print test1.

Check (test1 1).

Definition test2(n:nat) := fun (x:nat) => x.

Print test2.

Check test2.

Check (test2 1).

Check (test2 1 2).

Definition test3 := fun (x:nat) => x.

Check (test3 4).

Definition test4(X:Type) := fun (x:X) =>x.

Check (test4 bool true).

(******)
(* important *)
Definition test5 := nat->nat.
(* wrong *)
(* Check (test5 5). *)

Definition test6(x:bool) := bool->(nat->nat).

Check test6.
(* false *)
(* Check ((test6 true) true). *)

Definition test7 := fun (x:nat) => x.

Check (test7 5).



(* worng *)
(* Definition test8:nat := fun (x:nat) => x. *)

Definition test8:nat->nat := fun (x:nat) => x.


(* EXAMPLES *)
Module zbh.
Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

Definition total_map := id -> nat.

Definition t_empty (v : nat) : total_map :=
  (fun _ => v).

Check ((t_empty 4) (Id 4)).

Definition test10 (x:total_map) (y:id) := x y. 

Check (test10 ( fun (x:id) => 3) (Id 4)).

Compute  (test10 ( fun (x:id) => 3) (Id 4)). 

(* MUST BE WORNG *)
(* Check (total_map (Id 4)). *)

Definition t_update (m : total_map)
                    (x : id) (v :nat):total_map :=
  fun x' => if beq_id x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty 0) (Id 1) 100)
           (Id 3) 200.

Compute ((t_update (t_update (t_empty 0) (Id 1) 100)
           (Id 3) 200) (Id 1)).

Compute ((t_update (t_empty 0) (Id 1) 100)
           (Id 1)). 

Compute ((t_update (t_empty 0) (Id 1) 100)
           (Id 2)). 

Compute ((t_update (t_empty 0) (Id 1) 100)). 

End zbh.

(* Module xy. *)
(* Inductive id : Type := *)
(*   | Id : nat -> id. *)

(* Definition total_map := fun (x:id) => 3. *)

(* Definition t_empty (v : nat) : total_map := *)
(*   (fun (x:id) => 3). *)

(* Check ((t_empty 4) (Id 4)). *)

(* Definition test10 (x:total_map) (y:id) := x y.  *)

(* Check (total_map (Id 4)). *)


(* End zbh_test *)

(*
The difference of definition of Map is compute and relation.
Sometimes we just need the type is enough.
*)
