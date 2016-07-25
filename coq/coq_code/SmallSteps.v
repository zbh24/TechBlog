Inductive tm: Type :=
  | C: nat->tm
  | P: tm->tm->tm.

(* big step *)
Inductive bigstepeval:tm->nat->Prop :=
  | const:forall n,bigstepeval (C n) n
  | plus:forall t1 t2 n1 n2, bigstepeval t1 n1->
                              bigstepeval t2 n2->
                              bigstepeval (P t1 t2) (n1+n2).



Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

Reserved Notation " t '\\' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n \\ n
  | E_Plus : forall t1 t2 n1 n2,
      t1 \\ n1 ->
      t2 \\ n2 ->
      P t1 t2 \\ (n1 + n2)

  where " t '\\' n " := (eval t n).

(* small step *)
(* Reserved Notation " t '==>' t' " (at level 40). *)

(* Inductive step : tm -> tm -> Prop := *)
(*   | ST_PlusConstConst : forall n1 n2, *)
(*       P (C n1) (C n2) ==> C (n1 + n2) *)
(*   | ST_Plus1 : forall t1 t1' t2, *)
(*       t1 ==> t1' -> *)
(*       P t1 t2 ==> P t1' t2 *)
(*   | ST_Plus2 : forall n1 t2 t2', *)
(*       t2 ==> t2' -> *)
(*       P (C n1) t2 ==> P (C n1) t2' *)

(*   where " t '==>' t' " := (step t t'). *)


(**********************************)
Inductive value : tm -> Prop :=
  v_const : forall n, value (C n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->                     (* <----- n.b. *)
        t2 ==> t2' ->
        P v1 t2 ==> P v1 t2'

  where " t '==>' t' " := (step t t').

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
  induction t.
    - (* C *) left. apply v_const.
    - (* P *) right. inversion IHt1.
      + (* l *) inversion IHt2.
        * (* l *) inversion H. inversion H0.
          exists (C (n + n0)).
          apply ST_PlusConstConst.
        * (* r *) inversion H0 as [t' H1].
          exists (P t1 t').
          apply ST_Plus2. apply H. apply H1.
      + (* r *) inversion H as [t' H0].
          exists (P t' t2).
          apply ST_Plus1. apply H0.  Qed.


Definition relation (X: Type) := X->X->Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.


Theorem step_deterministic:
  deterministic step.
Proof.
Abort.


(**************************************)
(* Normal Form  *)
(*
To state this observation formally, let's begin by giving a name
    to terms that cannot make progress.  We'll call them _normal
    forms_.
*)
Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H. inversion H.
  intros contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t ==> t').
  { (* Proof of assertion *) apply strong_progress. }
  inversion G.
    + (* l *) apply H0.
    + (* r *) exfalso. apply H. assumption.  Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf. Qed.


(****************************)
(** * Multi-Step Reduction *)
Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.


(** ** Normal Forms Again *)

(** If [t] reduces to [t'] in zero or more steps and [t'] is a
    normal form, we say that "[t'] is a normal form of [t]." *)

Definition step_normal_form := normal_form step.


Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

Definition normal_form_of (t t' : tm) :=
  (t ==>* t' /\ step_normal_form t').



