Require Export IndProp.

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

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


Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)


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


(**         Programming with Tactics    **)

Definition add1 : nat ->  nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. 
Defined.

Print add1.
(* ==>
    add1 = fun n : nat => S n
         : nat -> nat
*)

Compute add1 2.
(* ==> 3 : nat *)

Module Props.

Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

End And.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  -
    intros [HP HQ]. split.
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


Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R
:=
fun (P Q R:Prop) (H1:P /\ Q) (H2:Q /\ R) => match H1 with
                                                | conj p _ => 
                                              match H2 with
                                                 | conj _ r => conj p r
                                               end
                                            end.

 

(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

Module Or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

End Or.

Check or_introl.
(* Check (or_introl (3=4)). *)
(* Check (fun (P Q:Prop) => or_introl). *)

Lemma test: forall P Q, P \/ Q -> Q \/ P.
Proof.
intros.
destruct H.
right.
apply H.
left.
apply H.
Qed.

Definition or_comm : forall P Q, P \/ Q -> Q \/ P
:= fun (P Q :Prop) => fun(H:P \/ Q) => 
                        match H with
                          | or_introl P => or_intror P
                          | or_intror Q => or_introl Q
                        end.


  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

End Ex.

Check ex (fun n => ev n).

Definition some_nat_is_even : ex (fun n => ev n) :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Definition some_nat_is_even_0 : ex (fun n => ev n) :=
  ex_intro (fun n => ev n) 0 ev_0.

Definition some_nat_is_even' : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
ex_intro (fun n => ev (S n)) 1 ((ev_SS 0 ev_0)) .

Lemma test_ex:exists n, ev n. (* ex ev *)
Proof.
refine (
ex_intro ev 0 ev_0
).
Qed.

Inductive True : Prop :=
  I : True.

Inductive False : Prop :=.

End Props.

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x:X, eq x x.

Notation "x = y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

Check eq_refl 3.

Check (eq 3 3).

Lemma leibniz_equality : forall (X : Type) (x y: X),
  x = y ->  forall P : X -> Prop, P x -> P y.
Proof.
intros.
destruct H.
apply H0.
Qed.

Lemma four: 2 + 2 = 1 + 3.
Proof.
  apply eq_refl.
Qed.

Definition four' : 2 + 2 = 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Set) (x:X), []++[x] = x::[] :=
  fun (X:Set) (x:X) => eq_refl [x].

End MyEquality.

Definition quiz6 : exists x, x + 3 = 4
  := ex_intro (fun z => (z + 3 = 4)) 1 (refl_equal 4).

Print Ltac exfalso.
