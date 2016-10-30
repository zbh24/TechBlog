(* To build an impredicative definition that simulates an inductive type
   following this technique:

  * construct a function that takes the same type of arguments as the 
    inductive type and returns a type, obtained in the following manner.

  + quantify over a predicate P that have the same type as the predicate
    one wants to simulate (excepted the parameters of the inductive type).

  + construct implications where premises state that the predicate P
    simulates the constructors of the inductive predicate.  In other words,
    each premise is a constructor of the inductive predicate where
    instances of the inductive predicate name are replaced with P.

  + the ultimate conclusion must express that P holds for the arguments
    (but the parameters do not appear).

  This definition actually expresses that the least property that satisfies
  the constructors holds. *)

(* For instance, for sorted lists: *)

Require Export List.

(* La définition inductive est la suivante: *)

Inductive sorted (A:Set)(R:A->A->Prop) : (list A)->Prop :=
  sorted0 : sorted A R nil
| sorted1 : forall x:A, sorted A R (x::nil)
| sorted2 : forall (x1 x2:A)(l':list A),
              R x1 x2 -> sorted A R (x2::l') -> sorted A R (x1::x2::l').

Definition impredicative_sorted (A:Set)(R:A->A->Prop)(l:list A) : Prop :=
  forall P : (list A)->Prop,
     P nil ->
     (forall x:A, P (x::nil))->
     (forall (x1 x2:A)(l':list A),
         R x1 x2 -> P (x2::l') -> P (x1::x2::l'))->
     P l.

(* To prove that the two predicates are equivalent we first need to show
   that the impredicative definition satisfies the constructors. *)

Theorem isorted0 : forall (A:Set)(R:A->A->Prop), impredicative_sorted A R nil.
Proof.
 unfold impredicative_sorted; auto.
Qed.

Theorem isorted1 :
 forall (A:Set)(R:A->A->Prop)(x:A), impredicative_sorted A R (x::nil).
Proof.
 unfold impredicative_sorted; auto.
Qed.

Theorem isorted2 :
 forall (A:Set)(R:A->A->Prop)(x1 x2:A)(l':list A),
    R x1 x2 ->
    impredicative_sorted A R (x2::l') ->
    impredicative_sorted A R (x1::x2::l').
Proof.
 intros A R x1 x2 l' Hr Hs P Hsn Hs1 Hs2.
 apply Hs2; auto.
 apply Hs; auto.
Qed.

Hint Resolve isorted0 isorted1 isorted2.
Hint Resolve sorted0 sorted1 sorted2.

(* The proof by induction on the inductive predicate require that
  we check that the other property actually satisfies the constructors. *)

Theorem sorted_to_i :
 forall A R l, sorted A R l -> impredicative_sorted A R l.
Proof.
 intros A R l H; elim H; auto.
Qed.

(* The impredicative definition also require checking that the other
   inductive definition satisfies the constructors. *)

Theorem impredicative_to_sorted :
 forall A R l, impredicative_sorted A R l -> sorted A R l.
Proof.
 intros A R l H; apply H; auto.
Qed.


(* If we want to simulate "less-or-equal" we can define the impredicative
   expression by again following the constructors. *)
Definition impredicative_le (n p:nat) : Prop :=
   forall P: nat -> Prop,
     P n ->
     (forall m:nat, P m -> P (S m)) ->
     P p.

(* We can prove it satisfies the constructors like le. *)
Theorem impredicative_le_n : forall n: nat, impredicative_le n n.
Proof.
  unfold impredicative_le; auto.
Qed.

Theorem impredicative_le_S : 
  forall n m:nat, impredicative_le n m -> impredicative_le n (S m).
Proof.
  intros n m Hle P Hn Hs; apply Hs; apply Hle; auto.
Qed.

Hint Resolve impredicative_le_n impredicative_le_S.

Theorem le_to_impredicative :
 forall n p, n <= p -> impredicative_le n p.
Proof.
 intros n p Hle; elim Hle; auto.
Qed.

Theorem impredicative_to_le :
 forall n p, impredicative_le n p -> n <= p.
Proof.
 intros n p H; apply H; auto.
Qed.

(* For disjunction, we do it in the same way, still giving the
   parameters a position outside the universal quantification. *)
Definition impredicative_or (A B:Prop) : Prop :=
  forall P:Prop, 
(* first constructor. *)
    (A -> P) ->
(* second constructor. *)
    (B -> P) ->
    P.

Theorem impredicative_or_intro1 :
  forall A B:Prop, A -> impredicative_or A B.
Proof.
 unfold impredicative_or; auto.
Qed.

Theorem impredicative_or_intro2 :
 forall A B:Prop, B -> impredicative_or A B.
Proof.
 unfold impredicative_or; auto.
Qed.

Hint Resolve impredicative_or_intro1 impredicative_or_intro2.

Theorem or_to_impredicative : forall A B, A \/ B -> impredicative_or A B.
Proof.
 intros A B H; elim H; auto.
Qed.

Theorem impredicative_to_or : forall A B, impredicative_or A B -> A \/ B.
Proof.
 intros A B H; apply H; auto.
Qed.
