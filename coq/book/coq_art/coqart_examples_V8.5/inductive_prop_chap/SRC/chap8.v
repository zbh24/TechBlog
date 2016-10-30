Require Export ZArith.
Require Export List.
Require Export Arith.
Require Export Omega.
Require Export Zwf.


(* taken from chapter 5 *)

Inductive plane : Set :=
    point : Z->Z->plane.

Inductive htree (A:Type) : nat->Type :=
  | hleaf : A -> htree A 0%nat
  | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).

Inductive south_west : plane->plane->Prop :=
  south_west_def :
  forall a1 a2 b1 b2:Z, (a1 <= b1)%Z -> (a2 <= b2)%Z -> 
        south_west (point a1 a2)(point b1 b2).

Inductive even : nat->Prop :=
  | O_even : even 0
  | plus_2_even : forall n:nat, even n -> even (S (S n)).

Inductive sorted (A:Set)(R:A->A->Prop) : list A -> Prop :=
  | sorted0 : sorted A R nil
  | sorted1 : forall x:A, sorted A R (cons x nil)
  | sorted2 :
      forall (x y:A)(l:list A),
        R x y ->
        sorted A R (cons y l)-> sorted A R (cons x (cons y l)).

Implicit Arguments sorted [A].
Hint Resolve sorted0 sorted1 sorted2 : sorted_base.

Require Export Relations.


Inductive clos_trans (A:Type)(R:relation A) : A->A->Prop :=
  | t_step : forall x y:A, R x y -> clos_trans A R x y
  | t_trans :
    forall x y z:A, clos_trans A R x y -> clos_trans A R y z -> 
        clos_trans A R x z.


Theorem sorted_nat_123 : sorted le (1::2::3::nil).
Proof.
 auto with sorted_base arith.
Qed.

Theorem xy_ord :
 forall x y:nat, le x y -> sorted  le (x::y::nil).
Proof.
 auto with sorted_base.
Qed.

Theorem zero_cons_ord :
 forall l:list nat, sorted le l -> sorted le (cons 0 l).
Proof.
 induction 1; auto with sorted_base arith.
Qed.

Theorem sorted1_inv :
 forall (A:Set)(le:A->A->Prop)(x:A)(l:list A),
   sorted  le (cons x l)-> sorted  le l.
Proof.
 inversion 1; auto with sorted_base.
Qed.

Theorem sorted2_inv :
 forall (A:Set)(le:A->A->Prop)(x y:A)(l:list A),
   sorted  le (cons x (cons y l))-> le x y.
Proof.
 inversion 1; auto with sorted_base.
Qed.

Theorem not_sorted_132 :  ~ sorted le (1::3::2::nil).
Proof.
 intros H;assert (H1:sorted le (3::2::nil)).
 apply sorted1_inv with (1:= H).
 assert (H2 : 3<=2).
 apply sorted2_inv with (1:= H1).
 omega.
Qed.

Check True_ind.

Check False_ind.

Check and_ind.

Check or_ind.

Check ex_ind.

Check eq_ind.

Require Import JMeq.

Check JMeq_eq.

Check JMeq_ind.


Inductive ahtree(A:Type) : Type :=
  any_height : forall n:nat, htree A n -> ahtree A.

Theorem any_height_inj2 :
 forall (A:Type)(n1 n2:nat)(t1:htree A n1)(t2:htree A n2),
   any_height _ n1 t1 = any_height _  n2 t2 -> JMeq t1 t2.
Proof.
 intros A n1 n2 t1 t2 H.
 injection H.
 intros H1 H2.
 dependent rewrite <- H1.
Restart.
intros A n1 n2 t1 t2 H.
 change (match any_height _ n2 t2 with
        | any_height _ n t => JMeq t1 t
        end);
   rewrite <- H.
 trivial. 
Qed.

Require Import List.
Require Import Vector.

Section vectors_and_lists.
 Variable A : Type.
Print t.
 Fixpoint vector_to_list (n:nat)(v:t A n){struct v} 
  : list A :=
  match v with
  | nil _ => List.nil 
  | cons _ a p tl => List.cons a (vector_to_list p tl)
  end.

 Fixpoint list_to_vector (l:list A) : t A (length l) :=
   match l as x return t A (length x) with
   | List.nil => nil A
   | List.cons a tl => cons A a (length tl)(list_to_vector tl)
   end.

 Theorem keep_length :
  forall (n:nat)(v:t A n), length (vector_to_list n v) = n.
 Proof.
   intros n v; elim v; simpl; auto.
 Qed.

 Lemma Vconseq :
  forall (a:A)(n m:nat),
   n = m ->
   forall (v:t A n)(w:t A m),
     JMeq v w -> JMeq (cons A a n v)(cons A a m w).
 Proof.
  intros a n m Heq; rewrite Heq.
  intros v w HJeq.
  elim HJeq; reflexivity.
 Qed. 

 Theorem vect_to_list_and_back :
  forall n (v:t A n),
    JMeq v (list_to_vector (vector_to_list n v)).
 Proof.
  intros n v; elim v.
  simpl; auto.
  intros a n' v' HJeq.
  simpl.
  apply Vconseq.
  symmetry; apply keep_length.
  assumption.
 Qed.

End vectors_and_lists.

Theorem structured_intro_example1 : forall A B C:Prop, A/\B/\C->A.
Proof.
 intros A B C [Ha [Hb Hc]].
 auto.
Qed.

Theorem structured_intro_example2 : forall A B:Prop, A \/ B/\(B->A)->A.
Proof.
 intros A B [Ha | [Hb Hi]].
 auto.
 auto.
Qed.

Theorem sum_even : forall n p:nat, even n -> even p -> even (n+p).
Proof.
 intros n; elim n.
 auto.
 intros n' Hrec p Heven_Sn' Heven_p.
Restart.
 intros n p Heven_n; elim Heven_n.
 trivial.
 intros x Heven_x Hrec Heven_p; simpl.
 apply plus_2_even; auto.
Qed.

Check le_ind.

Theorem lt_le : forall n p:nat, n < p -> n <= p.
Proof.
 intros n p H; elim H; repeat constructor; assumption.
Qed.


Open Scope Z_scope.
Inductive Pfact : Z->Z->Prop :=
  Pfact0 : Pfact 0 1
| Pfact1 : forall n v:Z, n <> 0 -> Pfact (n-1) v -> Pfact n (n*v).

Theorem pfact3 : Pfact 3 6.
Proof.
 apply Pfact1 with (n := 3)(v := 2).
 discriminate.
 apply (Pfact1 2 1).
 discriminate.
 apply (Pfact1 1 1).
 discriminate.
 apply Pfact0.
Qed.
 
Theorem fact_def_pos : forall x y:Z, Pfact x y ->  0 <= x.
Proof.
 intros x y H; elim H.
 auto with zarith.
 intros n v Hneq0 HPfact Hrec.
 omega.
Qed.

Check Zwf_well_founded. 

Check well_founded_ind. 

Theorem Zle_Pfact : forall x:Z, 0 <= x -> exists y:Z, Pfact x y.
Proof.
 intros x0.
 elim x0 using (well_founded_ind (Zwf_well_founded 0)).
 intros x Hrec Hle.
  elim (Zle_lt_or_eq  _ _ Hle).
 2:intros Heq; rewrite <- Heq; exists 1; constructor.
 intro Hlt; elim (Hrec (x-1)).
 intros x1 Hfact; exists (x*x1); apply Pfact1; auto with zarith.
 unfold Zwf; omega.
 omega.
Qed.

Section little_semantics.
 Variables Var aExp bExp : Set.
 Inductive inst : Set :=
 | Skip : inst
 | Assign : Var->aExp->inst
 | Sequence : inst->inst->inst
 | WhileDo : bExp->inst->inst.

 Variables
  (state : Set)
  (update : state->Var->Z -> option state)
  (evalA : state->aExp -> option Z)
  (evalB : state->bExp -> option bool).

 Inductive exec : state->inst->state->Prop :=
 | execSkip : forall s:state, exec s Skip s
 | execAssign :
    forall (s s1:state)(v:Var)(n:Z)(a:aExp),
     evalA s a = Some n -> update s v n = Some s1 ->
     exec s (Assign v a) s1
 | execSequence :
    forall (s s1 s2:state)(i1 i2:inst),
     exec s i1 s1 -> exec s1 i2 s2 ->
     exec s (Sequence i1 i2) s2
 | execWhileFalse :
    forall (s:state)(i:inst)(e:bExp),
     evalB s e = Some false -> exec s (WhileDo e i) s
 | execWhileTrue :
    forall (s s1 s2:state)(i:inst)(e:bExp),
     evalB s e = Some true ->
     exec s i s1 ->
     exec s1 (WhileDo e i) s2 ->
     exec s (WhileDo e i) s2.

 Theorem HoareWhileRule :
  forall (P:state->Prop)(b:bExp)(i:inst)(s s':state),
    (forall s1 s2:state,
      P s1 -> evalB s1 b = Some true -> exec s1 i s2 -> P s2)->
    P s -> exec s (WhileDo b i) s' ->
    P s' /\ evalB s' b = Some false.
 Proof.
  intros P b i s s' H Hp Hexec; elim Hexec.
 Restart.
  intros P b i s s' H Hp Hexec; generalize H Hp; elim Hexec.
 Restart.
  intros P b i s s' H.
  cut
   (forall i':inst,
     exec s i' s' ->
     i' = WhileDo b i -> P s -> P s' /\ evalB s' b = Some false); 
   eauto.
  intros i' Hexec; elim Hexec; try (intros; discriminate).
  intros s0 i0 e Heval Heq; injection Heq; intros H1 H2.
  match goal  with
  | id:(e = b) |- _ => rewrite <- id; auto
  end.
  intros;
   match goal with
   | id:(_ = _) |- _ => injection id; intros H' H''
   end.
    subst i0 b;eauto.
 Qed.

End little_semantics.

Open Scope nat_scope.

Inductive is_0_1 : nat->Prop :=
  is_0 : is_0_1 0 | is_1 : is_0_1 1.

Hint Resolve is_0 is_1 .

Lemma sqr_01 : forall x:nat, is_0_1 x -> is_0_1 (x * x).
Proof.
  induction 1; simpl; auto.
Qed.

Theorem elim_example : forall n:nat, n <= 1 -> n*n <= 1.
Proof.
 intros n H.
 elim sqr_01.
 auto.
 auto.
 inversion_clear H; auto.
 inversion_clear H0; auto.
Qed.

Print even.

Section bad_proof_for_inversion.

 Theorem not_1_even : ~even 1.
 Proof.
  red; intros H; elim H.
 Abort.

End bad_proof_for_inversion.

Theorem not_even_1 : ~even 1.
Proof.
 unfold not; intros H.
 inversion H.
Qed.

Theorem plus_2_even_inv : forall n:nat, even (S (S n))-> even n.
Proof.
 intros n H; inversion H.
 assumption.
Qed.

Theorem not_even_1' : ~even 1.
Proof.
 intro H.
 generalize (refl_equal 1).
 pattern 1 at -2.
 elim H.
 discriminate.
 discriminate 3.
Qed.

Theorem plus_2_even_inv' : forall n:nat, even (S (S n))-> even n.
Proof.
 intros n H.
 generalize (refl_equal (S (S n))); pattern (S (S n)) at -2.
 elim H.
 intros H1; discriminate H1.
 intros n0 H'0 H' H'1.
 injection H'1; intros H'2; rewrite <- H'2; assumption.
Qed.

