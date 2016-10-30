Set Implicit Arguments.
Require Export List.
Require Export Ltree.

CoFixpoint graft (A:Set) (t t':LTree A) : LTree A :=
  match t with
  | LLeaf => t'
  | LBin n t1 t2 => LBin n (graft t1 t') (graft t2 t')
  end.

