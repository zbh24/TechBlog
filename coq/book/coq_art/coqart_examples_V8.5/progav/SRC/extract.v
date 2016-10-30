Definition sig_extract (A:Set) (P:A -> Prop) (x:sig P) : A :=
  match x with
  | exist _ a Ha => a
  end.

Theorem sig_extract_ok :
 forall (A:Set) (P:A -> Prop) (y:sig P), P (sig_extract A P y).
Proof.
 intros A P y; case y; simpl; trivial.
Qed.

Require Import ZArith.
Open Scope Z_scope.

Parameter
  div_pair :
    forall a b:Z,
      0 < b ->
      {p : Z * Z | a = fst p * b + snd p  /\ 0 <= snd p < b}.

Definition div_pair' : forall a b:Z, 0 < b -> Z * Z.
 intros a b Hb.
 apply (sig_extract _ _ (div_pair a b Hb)).
Defined.

Theorem div_pair'_ok :
 forall (a b:Z) (H:0 < b),
   let p := div_pair' a b H in
   a = fst p * b + snd p /\ 0 <= snd p < b.
 intros a b H.
 pattern (div_pair' a b H).
 unfold div_pair'; apply sig_extract_ok.
Qed.

