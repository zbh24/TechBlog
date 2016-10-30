 Require Import Vector.


 Implicit Arguments cons [A n].
 Implicit Arguments nil [A].
 Implicit Arguments hd [A n].
 Implicit Arguments tl [A n].

Set Implicit Arguments.

Definition vec2 (A:Type) := t A 2.


Definition vcons2 (A:Type)(a b:A): vec2 A := cons a (cons b nil).

Implicit Arguments vcons2 [A].


(* we want to coerce any A-vector of length 2 into A*A
*)

 
Definition v2prod {A:Type}(v:vec2 A):(prod A A) :=
     (hd v, (hd (tl v))).


Lemma v2prod_ok : forall A (a b:A), v2prod  (vcons2 a b)=(a,b).
 Proof.
  reflexivity.
Qed.




Coercion v2prod : vec2 >-> prod.




Check (fst (vcons2 3 4)). 

Eval compute in (snd (vcons2 3 4)).





Definition Vid: forall (A:Type)(n:nat), t A n -> t A n.
 destruct n. intro v.
 exact nil.
 intro v; exact (cons (hd v) (tl v)).
Defined.





 Lemma Vid_eq : forall A n (v:t A n), v= Vid  v.
 Proof.
  destruct v; reflexivity.
Qed.

Lemma V0 : forall A (v:t A 0), v=nil.
Proof.
 intros A v.
 change (@nil A) with (Vid v).
 apply Vid_eq.
Qed.

Lemma VS : forall A n (v:t  A (S n)), v = cons (hd v) (tl v).
Proof.
 intros A n v.
 change (cons (hd v) (tl v)) with (Vid  v).
 apply Vid_eq.
Qed.

Lemma V2_0 : forall A (v:vec2 A), v =  vcons2 (hd v) (hd (tl v)). 
Proof.
 intros A v.
 pattern v at 1; rewrite  (VS  v).
 pattern (tl v) at 1; rewrite (VS (tl v)).
 unfold vcons2;rewrite <- (V0  (tl (tl v))).
 reflexivity.
Qed.

Lemma V2 : forall A (v:vec2 A), v= vcons2 (fst v) (snd v).
Proof.
 intros A v.
 generalize (V2_0 v).
 simpl.
 auto.
Qed.












 
