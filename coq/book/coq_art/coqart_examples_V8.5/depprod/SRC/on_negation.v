Lemma id_prop : forall P:Prop, P -> P.
Proof.
  auto.
Qed.

Theorem not_False : ~ False.
Proof id_prop False.


Lemma P3Q : forall P Q:Prop, (((P -> Q) -> Q) -> Q) -> P -> Q.
Proof.
 auto.
Qed.

Theorem triple_neg : forall P:Prop, ~ ~ ~ P -> ~ P.
Proof.
 intros P H; red; apply P3Q; assumption.
Qed.

Theorem P3PQ : forall P Q:Prop, ~ ~ ~ P -> P -> Q.
Proof.
 intros P Q H p.
 elim (triple_neg _ H p).
Qed.


Lemma imp_trans : forall P Q R:Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
 auto.
Qed.

Theorem contrap : forall P Q:Prop, (P -> Q) -> ~ Q -> ~ P.
Proof fun P Q:Prop => imp_trans P Q False.

Theorem imp_absurd : forall P Q R:Prop, (P -> Q) -> (P -> ~ Q) -> P -> R.
Proof.
 intros P Q R H H0 p.
 elim (H0 p (H p)).
Qed.


(* Using automatic tactics ... *)

Theorem not_false' : ~ False.
Proof.
 unfold not; auto.
Qed.


Theorem triple_neg' : forall P:Prop, ~ ~ ~ P -> ~ P.
Proof.
 unfold not; auto.
Qed.



Theorem P3PQ' : forall P Q:Prop, ~ ~ ~ P -> P -> Q.
Proof.
 tauto.
Qed.



Theorem contrap' : forall P Q:Prop, (P -> Q) -> ~ Q -> ~ P.
Proof.
 unfold not; auto.
Qed.

Theorem imp_absurd' : forall P Q R:Prop, (P -> Q) -> (P -> ~ Q) -> P -> R.
Proof.
 tauto.
Qed.
