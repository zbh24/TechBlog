Set Implicit Arguments.
Require Export List.
Require Export Ltree.


Require Export ZArith.

Open Scope positive_scope.

CoFixpoint PosTree (p:positive) : LTree positive :=
  LBin p (PosTree (xO p)) (PosTree (xI p)).


Eval compute in (LTree_label (PosTree 1) (d0 :: d1 :: nil)).

Eval compute in (LTree_label (PosTree 1) (d0 :: d1 :: d1 :: nil)).

Eval compute in (LTree_label (PosTree 1) 
                             (d0 :: d1 :: d1 :: d0 :: d0 ::d1 :: nil)).

CoFixpoint graft (A:Set) (t t':LTree A) : LTree A :=
  match t with
  | LLeaf => t'
  | LBin n t1 t2 => LBin n (graft t1 t') (graft t2 t')
  end.






