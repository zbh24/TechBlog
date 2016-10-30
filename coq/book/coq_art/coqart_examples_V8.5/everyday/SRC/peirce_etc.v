Lemma id_P : forall P:Prop, P -> P.
Proof.
 intros ; assumption.
Qed.

Lemma id_PP : forall P:Prop, (P -> P) -> P -> P.
Proof.
 intros; assumption. 
Qed.

Lemma imp_trans : forall P Q R :Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
 intros P Q R H H0 p; apply H0; apply H; assumption. 
Qed.

Lemma imp_perm :  forall P Q R :Prop, (P -> Q -> R) -> Q -> P -> R.
Proof.
 intros P Q R H q p ; apply H; assumption. 
Qed.

Lemma ignore_Q : forall P Q R :Prop, (P -> R) -> P -> Q -> R.
Proof.
 intros P Q R H p q; apply H; assumption. 
Qed.

Lemma delta_imp :  forall P Q :Prop,(P -> P -> Q) -> P -> Q.
Proof.
 intros P Q H p; apply H; assumption. 
Qed.

Lemma delta_impR :forall P Q :Prop, (P -> Q) -> P -> P -> Q.
Proof.
  intros P Q H p; apply H; assumption. 
Qed.

Lemma diamond : forall P Q R T:Prop, (P -> Q) -> 
                                  (P -> R) -> 
                                  (Q -> R -> T) -> 
                                  P -> T.
Proof.
 intros P Q R T H H0 H1 p; apply H1. 
 apply H; assumption. 
 apply H0; assumption.
Qed.

Lemma weak_peirce : forall P Q:Prop, ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
 intros P Q H ; apply H ; intro H0.
 apply H0; intro p; apply H.
 intro; assumption.
Qed.
