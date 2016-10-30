Set Implicit Arguments.
Require Export graft.



Definition LTree_decomp (A:Set) (t: LTree A) : LTree A
  := match t with
         LLeaf => LLeaf
       | LBin a t1 t2 => (LBin  a t1 t2)
       end.

Lemma LTree_decompose : 
   forall (A : Set) (t: LTree A), t = LTree_decomp t.
Proof.
 destruct t; trivial.
Qed.

Ltac  LTree_unfold term :=
  apply trans_equal with (1 := LTree_decompose term).


Lemma graft_unfold1 : forall (A:Set) (t': LTree A),
    graft LLeaf  t' = t'.
Proof.
 intros A t'; LTree_unfold (graft LLeaf t');
  case t'; simpl; auto.
Qed.

Lemma graft_unfold2: forall (A:Set)(a:A) (t1 t2 t':LTree A),
                      (graft (LBin a t1 t2) t')=
                      (LBin a (graft t1 t') (graft t2 t')).
Proof.
 intros A a t1 t2 t'; LTree_unfold (graft (LBin a t1 t2) t');
  simpl; auto.
Qed.


Lemma graft_unfold : forall (A:Set) (t t': LTree A),
                     graft t t' = match t  with
                                  | LLeaf => t'
                                  | LBin n t1 t2 =>
                                             LBin  n (graft t1 t')
                                                     (graft t2 t')
                                  end.
Proof.
 intros A t t'; case t.
 apply graft_unfold1. 
 intros; apply graft_unfold2.
Qed.


