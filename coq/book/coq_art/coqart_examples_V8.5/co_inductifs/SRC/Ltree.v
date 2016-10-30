(* (c) P. Casteran *)

Set Implicit Arguments.
Require Export List.

(* potentialy infinite trees with internal nodes labeled with type A *)

CoInductive LTree (A:Set) : Set :=
  LLeaf : LTree A
| LBin : A -> LTree A -> LTree A -> LTree A.

Implicit Arguments LLeaf [A].

Definition is_LLeaf (A:Set) (t:LTree A) : Prop :=
  match t with
  | LLeaf => True
  | _ => False
  end.

Definition L_root (A:Set) (t:LTree A) : option A :=
  match t with
  | LLeaf => None
  | LBin r _ _ => Some r
  end.

Definition L_left_son (A:Set) (t:LTree A) : option (LTree A) :=
  match t with
  | LLeaf => None
  | LBin _ t1 _ => Some t1
  end.

Definition L_right_son (A:Set) (t:LTree A) : option (LTree A) :=
  match t with
  | LLeaf => None
  | LBin _ _ t2 => Some t2
  end.

Inductive direction : Set :=
  | d0 : direction (* left *)
  | d1 : direction (* right *).


Definition path := list direction.


(* The subtree at path p *)

Fixpoint L_subtree (A:Set) (p:path) (t:LTree A) {struct p} :
 option (LTree A) :=
  match p with
  | nil => Some t
  | d0 :: p' =>
      match t with
      | LLeaf => None
      | LBin a t1 t2 => L_subtree p' t1
      end
  | d1 :: p' =>
      match t with
      | LLeaf => None
      | LBin a t1 t2 => L_subtree p' t2
      end
  end.


(* the label at path p *)
Inductive label (A:Set) : Set :=
  | node_label : A -> label A
  | leaf_label : label A.
    
Definition LTree_label (A:Set) (t:LTree A) (p:path) : 
  option (label A) :=
  match L_subtree p t with
  | None => None
  | Some t' =>
      match t' with
      | LLeaf => Some (leaf_label A)
      | LBin x _ _ => Some (node_label x)
      end
  end.


Lemma LTree_label_rw_leaf :
 forall (A:Set) (d:direction) (p:path), 
   LTree_label (LLeaf (A:=A)) (d :: p) = None.
Proof.
  unfold LTree_label in |- *; intros A d p; case d; simpl in |- *; auto.
Qed.


Lemma LTree_label_rw_root_bin :
 forall (A:Set) (a:A) (t1 t2:LTree A),
   LTree_label (LBin a t1 t2) nil = Some (node_label a).
Proof.
  unfold LTree_label in |- *; simpl in |- *; auto.
Qed.

Lemma LTree_label_rw_root_leaf :
 forall A:Set, LTree_label (LLeaf (A:=A)) nil = Some (leaf_label A).
Proof.
  unfold LTree_label in |- *; simpl in |- *; auto.
Qed.

Lemma LTree_label_rw0 :
 forall (A:Set) (a:A) (t1 t2:LTree A) (p:path),
   LTree_label (LBin a t1 t2) (d0 :: p) = LTree_label t1 p.
Proof.
  unfold LTree_label in |- *; simpl in |- *; auto.
Qed.

Lemma LTree_label_rw1 :
 forall (A:Set) (a:A) (t1 t2:LTree A) (p:path),
   LTree_label (LBin a t1 t2) (d1 :: p) = LTree_label t2 p.
Proof.
  unfold LTree_label in |- *; simpl in |- *; auto.
Qed.
