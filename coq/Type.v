Inductive sig (A:Set) (P:A -> Prop) : Set := exist (x:A) (_:P x).

Check (exist bool (fun x:bool => (1+1 = 2))).

Inductive sig' (A : Set) (P : A -> Prop) : Set :=
    exist' : forall x : A, P x -> sig' A P.

Inductive sig2 (A:Set) (P Q:A -> Prop) : Set := 
        exist2 (x:A) (_:P x) (_:Q x).


Inductive sigT (A:Type) (P:A -> Type) : Type := existT (x:A) (_:P x).

Inductive tree : Set :=
          node : forest -> tree
      with forest : Set :=
        | emptyf : forest
        | consf : tree -> forest -> forest.

Inductive even : nat -> Prop :=
        | even_O : even 0
        | even_S : forall n, odd n -> even (S n)
      with odd : nat -> Prop :=
        | odd_S : forall n, even n -> odd (S n).

Print All.

Inductive natq :Type :=
  | Q:natq
  | A:natq->natq.

Print nat_rect.
Print nat_ind.
Print nat_rec.

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

(* Wrong it is the wrong expression *)
Lemma nat_ind':forall P m n, P O -> (P n -> P (S n)) -> P m.
Proof.
intros P m n H1 H2.
(* You can find it is wrong the expression ,because the n fixed *)
Abort.

Lemma xx:forall n m,S n <= S m -> n <= m.