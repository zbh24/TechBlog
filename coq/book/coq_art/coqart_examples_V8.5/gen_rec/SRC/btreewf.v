Inductive tree (A:Set) : Set :=
  | leaf : tree A
  | node : A -> tree A -> tree A -> tree A.

Inductive tree_sub (A:Set) (t:tree A) : tree A -> Prop :=
  | tree_sub1 : forall (t':tree A) (x:A), tree_sub A t (node A x t t')
  | tree_sub2 : forall (t':tree A) (x:A), tree_sub A t (node A x t' t).

Theorem well_founded_tree_sub : forall A:Set, well_founded (tree_sub A).
Proof.
 intros A x; elim x.
 apply Acc_intro.
 intros y Hsub; inversion Hsub.
 intros a t1 Hrec1 t2 Hrec2; apply Acc_intro.
 intros y Hsub; inversion Hsub; auto.
Qed.
