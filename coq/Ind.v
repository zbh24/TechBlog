Lemma nat_ind0:forall P, P O -> (forall n ,P n -> P (S n)) -> (forall m,P m).
Proof.
refine (
fun P H1 H2 => _
).
(* intros P H1 H2. *)
refine (
    fix F m := match m with
      | O => H1
      | S m' => H2 m' (F m')
    end
).
Qed.


Lemma nat_ind1:forall P m, P O -> (forall n ,P n -> P (S n)) -> P m.
Proof.
intros.
refine ( (
    fix F n := match n with
      | O => X
      | S n' => X0 n' (F n')
    end
) m ).
Qed.

Lemma nat_ind2:forall P : nat -> Type,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n.
Proof.
refine (
fun (P : nat -> Type) (f : P 0) (f0 : forall n : nat, P n -> P (S n)) => _).
refine (
fix F (n : nat) : P n :=
  match n as n1 return (P n1) with
  | 0 => f
  | S n0 => f0 n0 (F n0)
  end
).
Qed.

Lemma test: forall n m ,n = m -> S n =  S m.
Proof.
Admitted.

(* Wrong: it is the wrong expression *)
Lemma nat_ind':forall P m n, P O -> (P n -> P (S n)) -> P m.
Proof.
(* intros P m n H1 H2. *)
(* You can find it is wrong the expression ,because the n fixed *)
intros P n m H1.
generalize dependent m.
(* refine ( ( *)
(*     fix F n := match n as n0 return P n0 with *)
(*       | O => H1 *)
(*       | S n' => H2 (F n') *)
(*     end *)
(* ) m ). *)
Abort.

Lemma xx:forall n m,S n <= S m -> n <= m.
Proof.
Admitted.

Lemma xx1: forall n m, n = m -> exists z1 z2 ,z1 = z2-> 
(n + z1 = m + z2).
Proof.
intros n m h1.
exists n.
exists n.
intros.

Print nat_rect.
Print nat_ind.
Print nat_rec.

(**************************************************)
Inductive unit : Set :=
  | tt.

Theorem unit_singleton : forall x : unit, x = tt.
Proof.
Show Proof.
(* induction x. *)
(* destruct x. *)
(* reflexivity. *)
(* refine *)
(* (fun u : unit => (u = tt)). *)
refine (
fun x : unit => match x as u return (u = tt) with
                | tt => eq_refl
                end
).
Qed.

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
  injection 1. 
trivial.
Qed.

Print nat_ind.
Theorem n_plus_O' : forall n : nat, plus n O = n.
  (* induction n. *) 
 apply nat_ind.
 Undo.
 apply (nat_ind (fun n => plus n O = n)) .
 Abort.

Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall : (nat -> formula) -> formula.

Example forall_refl : formula := Forall (fun x => Eq x x).

Fixpoint plus_recursive (n : nat) : nat -> nat :=
  match n with
    | O => fun m => m
    | S n' => fun m => S (plus_recursive n' m)
  end.

Definition plus_rec : nat -> nat -> nat :=
  nat_rec (fun _ : nat => nat -> nat) (fun m => m) (fun _ r m => S (r m)).

Theorem plus_equivalent : plus_recursive = plus_rec.
  reflexivity.
Qed.

Fixpoint nat_rect' (P : nat -> Type) 
  (HO : P O)
  (HS : forall n, P n -> P (S n)) (n : nat) :=
  match n as n0 return P n0 with
    | O => HO
    | S n' => HS n' (nat_rect' P HO HS n')
  end.

Lemma test1: forall n m , S n + m = S (n + m).
Proof.
intros.
generalize dependent m.
induction n.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Lemma test2: forall n m , S n + m = S (n + m).
Proof.
intros.
generalize dependent n.
induction m.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Lemma test3: forall m (P:nat-> Prop) (Q: nat-> Prop),  (forall n, P n -> Q m) ->((forall n, P n) -> Q m) .
Proof.
intros m P Q H1.
intros.
apply (H1 1).
apply (H 1).
Qed.

Lemma test4: forall m (P:nat-> Prop) ( Q: nat-> Prop), ((forall n, P n) -> Q m) -> (forall n, (P n -> Q m)).
Proof.
intros m P Q H1.
intros n H2.
apply H1.
Abort.

Lemma test5: forall m (P:nat-> Prop) ( Q: nat-> Prop), ((exists n, P n) -> Q m) -> (forall n, (P n -> Q m)).
Proof.
intros m P Q H1.
intros n H2.
apply H1.
exists n.
apply H2.
Qed.

Require Import Classical.
Lemma test6: forall (P :nat-> Prop) (Q:Prop), (exists n, (P n-> Q)) <-> ((forall n,P n) -> Q).
Proof.
split.
intros H1 H2.
destruct H1.
apply H.
apply (H2 x).

intros H1.
assert ((forall n, P n) \/ (exists n, ~ P n)).
destruct (classic (forall n, P n)).
left; auto.
right.
destruct (classic (exists n, ~ P n)).
auto.
exfalso.
assert (forall n, P n).
intros.
apply NNPP.
firstorder.
apply (H H2).
destruct H.
exists 0; intros. auto.
destruct H.
exists x.
intros. exfalso. apply (H H0).
Qed.

Lemma le1: forall (P :nat-> Prop) (Q:Prop), ((exists n, P n)-> Q) <-> (forall n,P n -> Q).
Proof.
split.
intros.
apply H.
exists n.
apply H0.

intros.
destruct H0.
apply (H x).
apply H0.
Qed.

Lemma le2: forall (P :nat-> Prop) (Q:Prop), ((forall  n, P n)-> Q) <-> (exists n,P n -> Q).
Proof.
split.
Abort.

(* This lemma is very important *)
Lemma le3 : forall (P:Prop) (Q:nat->Prop),(P->(forall n,Q n)) <-> (forall n,P-> Q n).
Proof.
split.
intros.
apply (H H0).

intros.
apply H.
apply H0.
Qed.

Lemma fq:forall (P:nat->Prop) (Q:Prop) ,(exists n, P n)->(exists n,~P n->Q).
Proof.
intros.
destruct H.
exists x.
intros.
exfalso.
apply (H0 H).
Qed.

(* Wrong:actually it is wrong *)
Lemma fq1:forall (P:nat->Prop) (Q:Prop) ,(exists n, P n)->(exists n,~P n)->Q.
Proof.
intros P Q H1.
destruct H1.
intros.
Abort.
