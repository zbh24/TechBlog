Require Export IndProp.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Theorem ev_8 : ev 8.
Proof.
  (* FILL IN HERE *) 
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition ev_8' : ev 8 :=
ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).


Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4':forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.

(*

When we view the proposition being proved by ev_plus4 as a function type, 

one aspect of it may seem a little unusual. The second argument's type, ev n, mentions the value of the first argument, n. 

While such dependent types are not found in conventional programming languages, 

they can be useful in programming too, 

as the recent flurry of activity in the functional programming community demonstrates.

Notice that both implication (→) and quantification (∀) correspond to functions on evidence. 

In fact, 

they are really the same thing: → is just a shorthand for a degenerate use of ∀ where there is no dependency, i.e., 


no need to give a name to the type on the left-hand side of the arrow.

For example, consider this proposition:

*)

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

(*

A proof term inhabiting this proposition would be a function with two arguments: 

a number n and some evidence E that n is even. 

But the name E for this evidence is not used in the rest of the statement of ev_plus2, 

so it's a bit silly to bother making up a name for it. We could write it like this instead, 

using the dummy identifier _ in place of a real name:

*)

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

(*

Or, equivalently, we can write it in more familiar notation:

*)

Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

(*
In general, "P → Q" is just syntactic sugar for "∀ (_:P), Q".
*)

Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

End And.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

Definition and_comm'_aux P Q (H : P /\ Q) :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

End Ex.

(**              MyEquality                     *)
Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x = y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

Check eq_refl 3.

Check (eq 3 3).

Lemma leibniz_equality : forall (X : Type) (x y: X),
  x = y ->  forall P : X -> Prop, P x -> P y.
Proof.