(* A sorting example : 
   (C) Yves Bertot, Pierre Castéran 
*)

(**
Proposition : supprimer sorted_b et le mettre en exo.

**)
Require Import List.
Require Import ZArith.
Require Import Bool.
Require Import Setoid.

Set Implicit Arguments.

(** A small polymorphic sorting function *)

(*** Definitions *)

Section A_fixed.
 Variable A : Type.
 Variable le_bool : A -> A -> bool.

 Fixpoint insert (a:A)(l:list A) : list A :=
 match l with nil => a::nil
            | b::l' => if le_bool a b then a::l else b::insert a l'
 end.

 Fixpoint insertion_sort (l:list A) : list A :=
 match l with nil => nil
            | a::l' => insert a (insertion_sort l')
 end.

 (* A boolean predicate for testing ... *)
 Fixpoint sorted_b (l:list A) : bool :=
 match l with nil => true
            | a::nil => true
            | a::((b::l') as l0) => le_bool a b && sorted_b l0
 end.





(** Since tests are just tests, we want to specify and prove formally
    our function insertion_sort *)

(** let us consider some binary relation on some type A *)

Section Correctness.
Require Import Relations.
 
Variable  leA : relation A.

Notation "x <=A y" := (leA x y) (at level 70, no associativity).

 Hypotheses (leA_total : forall a b, a <=A b \/ b <=A a) 
            (leA_le_bool_equiv : forall a b:A, le_bool a b = true <-> a <=A b).


(* Here is a logical specification of being sorted wrt/leA *)

Inductive sorted : list A -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall a:A, sorted (a :: nil)
  | sorted2 :
      forall ( a b :A) (l:list A),
        a <=A b ->
        sorted (b :: l) -> sorted (a :: b :: l).

(** List permutations *)

Let eqA_b (a b:A) := le_bool a b && le_bool b a.

Fixpoint nb_occ (a:A) (l:list A): nat :=
  match l with
  | nil => 0
  | (b :: l') => if eqA_b a b
                 then S (nb_occ a l')
                 else nb_occ a l'
  end.

(* list l' is a permutation of list l *)

Definition permutation (l l':list A) := 
    forall a:A, nb_occ a l = nb_occ a l'.

Definition sort_spec (f:list A-> list A):= forall l, let l' := f  l in
                                            sorted l' /\ permutation l l'.



(*** Proofs *)

Lemma le_bool_false : forall a b, le_bool a b = false -> le_bool b a = true.
Proof.
 intros a b; case (leA_total a b);intros H H0.
 rewrite <- leA_le_bool_equiv in H.
 rewrite H0 in H;discriminate.
 rewrite leA_le_bool_equiv;assumption.
Qed.


Hint Resolve sorted0 sorted1 sorted2 le_bool_false: sort.


(*Lemma sorted_b_2 : forall a b l, sorted_b  (a::b::l) = le_bool a b &&
                                                             sorted_b  (b::l).
  simpl.
  intros;reflexivity.
 Qed.
*)
Lemma sorted_sorted_b : forall l, sorted_b  l = true <-> sorted l.
Proof.
  induction l.
  simpl.
  split;auto with sort.
  destruct l.
  simpl.
  split;auto with sort.
  replace (sorted_b (a :: a0 :: l)) with 
          (le_bool a a0 &&  sorted_b  (a0::l));[|simpl;auto].
  split;intro H.
 constructor 3.
 rewrite andb_true_iff in H;destruct H.
 rewrite <- leA_le_bool_equiv;assumption.
 rewrite <- IHl.
  rewrite andb_true_iff in H;destruct H;auto.
  inversion H.  
 rewrite andb_true_iff.

split.
rewrite  leA_le_bool_equiv;assumption.
rewrite IHl;auto.
Qed.




Lemma insert_sorted :
 forall (l:list A) (x:A), sorted l -> sorted (insert x l).
Proof.
 intros l x H; elim H; simpl; auto with sort.
 intro a;case_eq (le_bool x a).
 constructor 3;auto with sort.
 rewrite  <- leA_le_bool_equiv;assumption.
 intro H1;apply le_bool_false in H1;auto with  sort.
  constructor 3.
 rewrite  <- leA_le_bool_equiv;assumption.
 auto with sort.
 intros a b l0; case_eq (le_bool x a); case_eq (le_bool x b);simpl;intros;auto with sort.
 constructor 3.
 rewrite  <- leA_le_bool_equiv;auto with sort.
 constructor 3; auto with sort. 
  constructor 3.
rewrite  <- leA_le_bool_equiv;assumption.
  constructor 3;auto.
 constructor 3;auto with sort.
 rewrite  <- leA_le_bool_equiv;auto with sort.
Qed.
 
Lemma insertion_sort_sorts : forall l, sorted (insertion_sort  l).
induction l; simpl insertion_sort;auto with sort.
apply insert_sorted;auto.
Qed.


Lemma permutation_refl : forall l:list A, permutation l l.
Proof.
 unfold permutation; trivial.
Qed.

Lemma permutation_transpose :
 forall (a b:A) (l l':list A),
   permutation l l' -> 
   permutation (a :: b :: l) (b :: a :: l').
Proof.
 intros a b l l' H c; simpl.
 case_eq (eqA_b c a); case_eq (eqA_b c b); 
  simpl; case (H c); auto.
Qed.

Lemma permutation_cons :
 forall (a:A) (l l':list A), permutation l l' -> 
                             permutation (a :: l) (a :: l').
Proof.
 intros a l l' H b.
 simpl; case_eq (eqA_b b a); auto. 
Qed.



Lemma permutation_trans : transitive (list A) permutation.
Proof.
 intros l l' l'' H H0 a; eapply trans_eq; eauto.
Qed.





Hint Resolve permutation_cons permutation_refl permutation_transpose : sort.


Lemma insert_permutation : forall (x:A)(l:list A),
                  permutation (x :: l) (insert   x l).
Proof with (auto with sort).
 induction l as [|a l0 H]; simpl...  
  case_eq (le_bool x a);simpl ...
 intro H0; apply permutation_trans with (a :: x :: l0) ...
Qed.

Hint Resolve insert_permutation : sort.

Lemma sort_permutation : forall l, permutation l (insertion_sort  l).
Proof with (auto with sort).
  induction l;simpl insertion_sort ...
  apply permutation_trans with (a::insertion_sort  l) ...
Qed.

Theorem sort_ok : sort_spec (insertion_sort ).
split.
apply insertion_sort_sorts.
apply sort_permutation.
Qed.

End Correctness.

End A_fixed.

Check insertion_sort.



(* Tests *)

Require Import ZArith.
Open Scope Z_scope.

Eval vm_compute in insert Zle_bool 4 (3::5::8::nil).
Eval vm_compute in insert Zle_bool 4 (5::3::8::nil).

Eval vm_compute in insertion_sort Zle_bool  (10::2::5::2::8::nil).

Eval vm_compute in insertion_sort Zge_bool  (10::2::5::2::8::nil).

Definition lex_Z_bool (x y:Z*Z) := 
  match x,y with (a,b),(c,d) => Zlt_bool a c || (Zeq_bool a c && Zle_bool c d)
  end.

Eval vm_compute in insertion_sort lex_Z_bool  ((15,10)::(2,5)::(3,8)::nil).
Eval vm_compute in sorted_b lex_Z_bool (insertion_sort lex_Z_bool  ((15,10)::(2,5)::(3,8)::nil)).

Definition cpt_Z_bool (x y:Z*Z) := 
  match x,y with (a,b),(c,d) => Zle_bool a c && Zle_bool b d
  end.

Eval vm_compute in insertion_sort cpt_Z_bool  ((3,0)::(4,3)::(5,2)::(2,5)::(3,8)::(3,7)::nil).



Eval vm_compute in sorted_b lex_Z_bool (insertion_sort lex_Z_bool   ((3,0)::(4,3)::(5,2)::(2,5)::(3,8)::(3,7)::nil)).




Close Scope Z_scope.


Check sort_ok.
Print sort_spec.


Extraction "insert-sort" insert insertion_sort.


Extraction Language Scheme.  
Extraction "insertion-sort" insert insertion_sort.


