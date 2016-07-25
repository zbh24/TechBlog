Require Import Coq.Arith.Arith.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

(* Poly map  *)
Definition total_map (X:Type) := id -> X.

(* Definition total_map' (X:Type) : id->X := fun _ => .  *)

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :total_map A :=
  fun x' => if beq_id x x' then v else m x'.

(*Poly map*)

Definition examplemap :=
  t_update (t_update (t_empty false) (Id 1) false)
           (Id 3) true.


Example sss := t_empty false (Id 3).

Compute ((t_update (t_update (t_empty false) (Id 1) false)
           (Id 3) true (Id 3)) ).

Compute ((t_update (t_update (t_empty false) (Id 1) false)
           (Id 3) true (Id 1)) ).

(*----------------------------------------------------------------*)
Inductive partial_map : Type :=
  | empty : partial_map
  | record : id-> nat-> partial_map-> partial_map.
  
Definition update (d : partial_map) (key : id) (value : nat): partial_map :=
  record key value d.

Definition examplemap1 :=
  update (update empty (Id 1) 100 )
           (Id 3) 200.

Fixpoint find (key : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record k v d' => if beq_id key k then Some v else find key d'
 end.