(* unordered pairs  *)

Require Import DecidableType.
Require Import DecidableTypeEx.

Module Upair (M: DecidableType)  <: DecidableType 
with  Definition t := (M.t* M.t)%type.

Definition t := (M.t * M.t)%type.


Definition eq(p p':t) : Prop :=
       M.eq (fst p) (fst p') /\ M.eq (snd p) (snd p')
    \/ M.eq (fst p) (snd p') /\ M.eq (snd p) (fst p').


Lemma  eq_refl : forall x : t, eq x x.
Proof.
  destruct x ;left;simpl;auto.
Qed.

Lemma  eq_sym : forall x y : t, eq x y -> eq y x.
Proof.
 intros (x0,x1) (y0,y1) [(H1,H2)|(H1,H2)]; simpl in H1,H2;
 [left|right];split;auto.
Qed.
 
 
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof.
 intros (x0,x1) (y0,y1) (z0,z1) [(H1,H2)|(H1,H2)] [(H3,H4)|(H3,H4)];
 simpl in * ;
 [left|right|right|left];eauto.
Qed.


Definition eq_dec :forall x y : t, { eq x y } + { ~ eq x y }.
destruct x as (t0, t1);destruct y as (t2,t3).
case (M.eq_dec t0 t2).
intro e; case (M.eq_dec t1 t3).
 left;red. left; simpl;auto. 
 intro n; right;red.
 intros [(H1,H2)|(H1,H2)];simpl in *.
 firstorder.
 case n.
 apply M.eq_trans with t2;auto.
 apply M.eq_trans with t0;auto.
 intro n.
  case (M.eq_dec t0 t3);intro H.
 case (M.eq_dec t1 t2);intro H1.
 left.
 right;simpl; auto.
 right; intros [(H2,H3)|(H2,H3)]; simpl in *; firstorder.
 right;
 intros [(H2,H3)|(H2,H3)]; simpl in *; firstorder.

Defined.


End Upair.

Locate eq_dec.



(* exemple *)
Require Import ZArith.
Module Zpair := Upair Z_as_DT.

Recursive Extraction Zpair.eq_dec.

Open Scope Z_scope.


Check (5,6).



Eval compute in (if Zpair.eq_dec  (5,6) (4+2,5) then true else false).

