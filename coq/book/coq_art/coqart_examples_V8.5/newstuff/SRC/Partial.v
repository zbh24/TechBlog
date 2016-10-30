Require Import Ensembles.

Set Implicit Arguments.

(** A partial function is characterized by a domain, a codomain,
  and a total function *)

Record partial_function (A B : Type) : Type := {
  domain : Ensemble A ;
  codomain : Ensemble B;
  ap : A -> B;
  domain_ok : forall a, In _ domain a -> In _ codomain (ap a)}.

(** Equality on partial functions *)
 
Inductive pfun_eq (A B : Type)(F G : partial_function A B) :
 Prop :=
 mk_pfun_eq : domain F = domain G ->
              codomain F = codomain G ->
              (forall a, In _ (domain F) a ->
                         ap F a = ap G a) ->
              pfun_eq F G.


(** equality on partial functions is Leibniz equality  *)

Axiom pfun_extensionality : forall (A B : Type)
                                   (F G : partial_function A B),
                                    pfun_eq F G -> F = G.



(* solution *)

Definition F1 : partial_function nat nat . 
  esplit with (fun n : nat => 0 < n)
              (Full_set nat) 
              (fun n: nat => n).
 split.
Defined.

Definition F2 : partial_function nat nat . 
  esplit with (fun n : nat => 0 < n)
              (Full_set nat) 
              (fun n: nat => match n with 0 => 1 | _ => n end).
 destruct a; split.
Defined.

Lemma F1_F2_eq : pfun_eq F1 F2.                             
 split.
 unfold F1, F2;auto.
 unfold F1, F2;auto.
 inversion 1.
 simpl;auto.
 simpl;auto.
Qed.

Lemma same_fun : ap F1 = ap F2.
replace F2 with F1.
 auto.
 apply pfun_extensionality.
 apply F1_F2_eq.
Qed.


Theorem zero_one : 0 = 1.
 change (ap F1 0 = ap F2 0).
 rewrite same_fun.
 auto.
Qed.




 
 
                         
