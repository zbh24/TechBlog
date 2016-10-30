Require Export List.

Inductive sorted (A:Set)(R:A->A->Prop) : list A -> Prop :=
  | sorted0 : sorted A R nil
  | sorted1 : forall x:A, sorted A R (cons x nil)
  | sorted2 :
      forall (x y:A)(l:list A),
        R x y ->
        sorted A R (cons y l)-> sorted A R (cons x (cons y l)).


Definition sorted' (A:Set)(R:A->A->Prop)(l:list A) :=
  forall (l1 l2:list A)(n1 n2:A),
    l = app l1 (cons n1 (cons n2 l2))-> R n1 n2.

Theorem sorted'0 : forall A R, sorted' A R nil.
Proof.
  intros A R l1 l2 n1 n2;
  case l1; simpl; intros; discriminate.
Qed.

Theorem sorted'1 : forall A R x, sorted' A R (x::nil).
Proof.
  intros A R x l1 l2 n1 n2; case l1.
  simpl; intros; discriminate.
  intros a l1'; case l1'; simpl; intros; discriminate.
Qed.

Theorem sorted'2 :
      forall (A:Set)(R:A->A->Prop) x y l,
        R x y ->
        sorted' A R (cons y l)-> sorted' A R (cons x (cons y l)).
Proof.
 intros A R x y l Hr Hs l1; case l1.
 intros l2 n1 n2 Heq; injection Heq; intros; subst; trivial.
 simpl; intros a l1' l2 n1 n2 Heq; injection Heq.
 intros Heq' Heqx; apply (Hs l1' l2); trivial.
Qed.

Hint Resolve sorted'0 sorted'1 sorted'2.

Theorem sorted_imp_sorted' :
 forall A R l, sorted A R l -> sorted' A R l.
Proof.
 intros A R l H; elim H; auto.
Qed.

Theorem sorted'_imp_sorted: forall A R l, sorted' A R l -> sorted A R l.
Proof.
 intros A R l; elim l.
 intros; apply sorted0.
 intros a l'; case l'.
 intros; apply sorted1.
 intros b l'' IHcons_b_l'' Hs'.
 apply sorted2.
 apply (Hs' nil l''); auto.
 apply IHcons_b_l''; intros l1 l2 n1 n2 Heq; apply (Hs' (a::l1) l2).
 rewrite Heq; auto.
Qed.
