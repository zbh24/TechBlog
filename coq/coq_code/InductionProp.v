Require Import Coq.omega.Omega.

Inductive grace:nat->Type :=
  | rule0 : grace 0 
  | rule1 : forall n:nat, grace n-> grace (n+3)
.

Inductive xq:nat->Type :=
  | r0 : xq 0 
  | r1 : forall n:nat, xq n-> xq (n+3)
  | r2: forall n:nat,xq n -> xq (n+5)
.

(* Fixpoint beq_nat (n m : nat) : bool := *)
(*   match n with *)
(*   | O => match m with *)
(*          | O => true *)
(*          | S m' => false *)
(*          end *)
(*   | S n' => match m with *)
(*             | O => false *)
(*             | S m' => beq_nat n' m' *)
(*             end *)
(*   end. *)

Lemma xxx:forall n:nat,(grace n) -> exists k , (n = 3*k).
Proof.
intros n H.
induction H as [| n' E' IH'].
exists 0.
simpl.
reflexivity.
destruct IH' as [k1 IH''].
rewrite IH''.
exists (S k1).
symmetry.
simpl.
omega.
Qed.

Lemma yyy:forall n:nat,(xq n) -> exists k , or (n = 3*k) (n = 5*k).
Proof.
intros n H.
induction H as [| n' E' IH' | n' E' IH'].
exists 0.
simpl.
left.
reflexivity.
destruct IH' as [k1 IH''].
exists (S k1).
left.
inversion IH''.
rewrite H.
omega.
rewrite H.
(* omega. *)
(* This lemma is wrong! *)
Abort.

Inductive xye:nat->Type :=
  | re0 : xye 6 
  | re1 : forall n:nat, xye n-> xye (n*3)
  | re2: forall n:nat, xye n -> xye (n*2)
.

Lemma zzz:forall n:nat, (xye n) -> exists k , or (n = 3*k) (n = 2*k).
Proof.
intros n H.
induction H as [|n' H' IH' | n' H' IH'].
exists 2.
left.
omega.
destruct IH' as [K'' IH''].
try (inversion IH'';
rewrite H;
exists  ( K''*3)).
left.
omega.
right.
omega.
destruct IH' as [K'' IH''].
try (inversion IH'';
rewrite H;
exists  ( K''*2)).
left.
omega.
right.
omega.
Qed.

Inductive xyr:nat->Prop :=
  | xy0 : xyr 1
  | xy1 : xyr 2
  | xy2: forall n m :nat, xyr n -> xyr m -> xyr (n+m)
.

Lemma aaa:forall n:nat, (xyr n) -> exists k ,(n = 1*k).
Proof.
intros n H.
induction H as [| | n' m' EN IHN EM IHM].
exists 1.
simpl.
omega.
exists 2.
omega.
destruct IHN as [k1 ihn].
destruct IHM as [k2 ihm].
exists (k1+k2).
subst.
omega.
Qed.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
    - (* ST_PlusConstConst *) inversion Hy2.
      + (* ST_PlusConstConst *) reflexivity.
      + (* ST_Plus1 *) inversion H2.
      + (* ST_Plus2 *) inversion H2.
    - (* ST_Plus1 *) inversion Hy2.
      + (* ST_PlusConstConst *) rewrite <- H0 in Hy1. inversion Hy1.
      + (* ST_Plus1 *)
        rewrite <- (IHHy1 t1'0).
        reflexivity. assumption.
      + (* ST_Plus2 *) rewrite <- H in Hy1. inversion Hy1.
    - (* ST_Plus2 *) inversion Hy2.
      + (* ST_PlusConstConst *) rewrite <- H1 in Hy1. inversion Hy1.
      + (* ST_Plus1 *) inversion H2.
      + (* ST_Plus2 *)
        rewrite <- (IHHy1 t2'0).
        reflexivity. assumption.
Qed.
