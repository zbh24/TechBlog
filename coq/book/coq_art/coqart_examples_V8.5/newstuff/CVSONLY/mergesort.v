(*http://www.labri.fr/perso/casteran/CoqArt/newstuff/mergesort.html *)
(* An exercise from Epigram tutorial *)
(* Pierre Castéran, Julien Forest *)

Require Import List.
Require Import Wf_nat.
Require Import Recdef.
Require Import Compare_dec.
Require Import Arith.
Require Import Peano_dec.
Require Import Omega.

  
(* sorting lists of natural numbers *)

Inductive sorted : list nat -> Prop :=
  sorted_nil : sorted nil
| sorted_single : forall n, sorted (n::nil)
| sorted_cons : forall n p l, n <= p -> sorted (p::l) -> sorted (n::p::l).

Fixpoint how_many (n:nat)(l:list nat){struct l}:nat :=
  match l with
  | nil => 0
  | p::l' => if eq_nat_dec n p then S (how_many n l') 
                               else how_many n l'
  end.

Definition permutation (l l':list nat) :=
 forall n, how_many n l = how_many n l'.

Definition sort (l l':list nat) :Prop := sorted l' /\
                                         permutation l l'.

(* (N,L) trees :
    binary trees whose leaves are labeled by L and nodes by N *)

Inductive tree(N L:Type):Type :=
  Leaf : L -> tree N L
| Node : N -> tree N L -> tree N L -> tree N L.

(* number of non None leaves in a (N, option L) tree *)

Function filled_leaves (N L:Type)(t:tree N (option L)){struct t} : nat :=
 match t with
   Leaf _ _ None => 0
   | Leaf _ _ (Some n) => 1
   | Node _ _ _ t1 t2 => filled_leaves N L t1 + filled_leaves N L t2
 end.

(* A (bool,L) tree is balanced if every node labeled with true has 
   the same number of real leaves in both subtrees, and every
   node labeled with false has one more real leave in its left son
   than its right son *)


Inductive balanced(L:Type): tree bool (option L) -> nat -> Prop :=
  bal_none :  balanced   L (Leaf  _ _ (None)) 0
| bal_some : forall l, balanced  L (Leaf _ _ (Some l)) 1
| bal_eq : forall t1 t2 n, balanced  L  t1 n -> balanced  L t2 n ->
                           balanced  L  (Node _ _ true t1 t2) (  2 * n)
| bal_diff : forall t1 t2 n , balanced  L t1 (S n) ->
                               balanced  L  t2 n ->
                               balanced  L (Node _ _ false t1 t2) (S ( 2 * n)).



(* insertion of a label in  balanced tree *)

Function insert (L:Type)(l:L)(t: tree bool (option L)) {struct t} :
                             tree bool (option L):=
   match t with 
          Leaf _ _ None => Leaf _ _ (Some l)
         |Leaf _ _ (Some b) => Node _ _ true (Leaf _ _ (Some b)) 
                                         (Leaf _ _ (Some l))
         |Node  _ _ true  t1 t2 =>
             Node _ _ false (insert L l t1) t2
         |Node _ _ false  t1 t2 =>
             Node _ _ true t1  (insert L l t2)
   end.

(* transforms a list into a balanced tree *)

Function share (L:Type)(l:list L)  {struct l}: tree bool (option L) :=
  match l with
    nil => Leaf _ _ None
  | (a::l') => insert _ a (share L l')
  end.

(* merging a pair of lists *)

Function pair_merge (ls : list nat * list nat) 
         {measure  (fun ls => length (fst ls)+ length (snd ls))} : list nat :=
 match ls with 
   (nil,nil) => nil
  | (nil,l )=> l
  | (l,nil) => l
  | (x1::l1,x2::l2) => if le_lt_dec x1 x2 
                       then x1::(pair_merge(l1,x2::l2))
                      else  x2::(pair_merge(x1::l1,l2))
  end.
Proof.
 intros;simpl.
 auto with arith.
 simpl;auto with arith.
Qed.

Definition merge l1 l2 := pair_merge (l1,l2).


Function flatten (t: tree bool (option nat)) : list nat :=
 match t with
   Leaf _ _ None => nil
 | Leaf _ _ (Some n) => n::nil
 | Node _ _ _ t1 t2 => merge (flatten t1) (flatten t2)
end.

Definition mergesort (l:list nat):list nat :=
  flatten (share _ l).


Lemma balanced_filled_leaves : forall L t n, balanced L  t n ->
                                             filled_leaves _ L t = n.

  intros L t; functional induction (filled_leaves  _ L t).
  (* first branch of filled_leaves *)
  inversion_clear 1;reflexivity.
  (* second branch of filled_leaves *)
  inversion_clear 1;reflexivity.
  (* third branch of filled_leaves *)
  inversion_clear 1.
  rewrite (IHn _ H0);rewrite (IHn0 _ H1);simpl;auto with arith.
  rewrite (IHn _ H0);rewrite (IHn0 _ H1);simpl;auto with arith.
Qed.


Lemma balanced_inv_eq :
 forall L t1 t2 n, balanced  L (Node _ _ true t1 t2) n ->
                 filled_leaves _ L t1 =  filled_leaves _ L t2.
Proof.
 inversion_clear 1.
 rewrite (balanced_filled_leaves  _ _ _ H0).
  rewrite (balanced_filled_leaves  _ _ _ H1);auto.
Qed.

Lemma balanced_inv_diff :
 forall L t1 t2 n, balanced  L (Node _ _ false t1 t2) n ->
                 filled_leaves _ L t1 =  S(filled_leaves _ L t2).
Proof.
 inversion_clear 1.
 rewrite (balanced_filled_leaves  _ _ _ H0).
  rewrite (balanced_filled_leaves  _ _ _ H1);auto.
Qed.

Function how_many_in_tree (n:nat)(t:tree bool (option nat)){struct t} : nat:=
 match t with
  Leaf _ _ None => 0
 |Leaf _ _  (Some p) => if eq_nat_dec n p then 1 else 0
 |Node _ _ _ t1 t2 =>   how_many_in_tree n t1 +   how_many_in_tree n t2
 end.  


(* lemmas about insert *)

Lemma insert_balanced : forall (L:Type)(a:L)(t: tree bool (option L)) n,
        balanced   _ t n -> 
        balanced   _ (insert _ a t) (S n).
Proof.
  intros L a t; functional induction (insert L a t).
  (* first branch of insert *)
  inversion_clear 1;constructor.
  (* second branch of insert *)
  inversion_clear 1.
  change 2 with (2*1);repeat  constructor.
  (* third branch of insert *)
  inversion_clear 1.
  constructor; auto.
  (* fourth branch of insert *)
  inversion_clear 1.
  replace  (S (S (2 * n0))) with (2 * (S n0)) by omega. 
  constructor; auto.
Qed.



Lemma share_balanced : forall (L:Type)(l:list L),
                        balanced L (share _ l) (length l).
Proof.
  intros L l; functional induction (share _ l).
  (* first branch of share *)
  constructor.
  (* second branch of share *)
  simpl;apply insert_balanced.
  assumption.
Qed.


(* About sorted lists *)


Lemma sorted_single_cons: forall l , sorted l ->
                           forall x,
                           (forall y, In y l -> x <= y) ->
                           sorted (x::l).
Proof.
 induction l.
 intros;constructor.
 intros;constructor.
 generalize (H0 a).
 intro H1;apply H1;auto.
 constructor.
 auto.
 auto.
Qed.

Lemma sorted_trans : forall l a x, sorted (a::l) -> x <= a -> sorted (x::l).
Proof.
 inversion_clear 1.
 intro;constructor.
 intro;constructor.
 eauto with arith.
 auto.
Qed.

Lemma sorted_inv_In : forall l x, sorted (x::l) -> forall y, In y l -> x<=y. 
Proof.
 induction l.
 inversion 2.
 intros.
 case  (in_inv H0). 
 intro;subst y;inversion_clear H;auto.
 intros; eapply IHl.
 inversion H.
 apply sorted_trans with a;auto.
 auto.
Qed.

(* merging lists *)
 
Lemma In_merge_inv : forall (ls : list nat * list nat) (n:nat),
                    In  n (pair_merge ls) -> In n (fst ls) \/ In n (snd ls).
Proof.
 intros ls n ;functional induction (pair_merge ls).
 simpl.
 contradiction.
 right;simpl;auto.
 left;simpl;auto.
 intro.
 case (in_inv H).
 intro;subst n.
 left;simpl;auto.
 intro H1;case (IHl H1).
 simpl.
 auto.
 simpl;auto.
 simpl.
 destruct 1.
 auto.
 case (IHl H).
 simpl;auto.
 simpl;auto.
Qed.
 

Lemma sorted_merge : forall ls, sorted (fst ls) -> sorted (snd ls) ->
                      sorted (pair_merge ls).
Proof.
 intros; functional induction (pair_merge ls).
 constructor.
 simpl in H0;auto.
 simpl in H;auto.
 simpl in H;simpl in H0.
 simpl in IHl.
 apply sorted_single_cons.
 apply IHl.
 inversion H;auto.
 constructor.
 auto.
 intros.
 case ( In_merge_inv _ _ H1).
 simpl.
 intros;eapply sorted_inv_In;eauto.
 simpl.
 destruct 1.
 subst y;auto.
 apply le_trans with x2.
 auto.
 eapply sorted_inv_In;eauto.
 simpl in *.
 apply sorted_single_cons.
 apply IHl.
 auto.
 inversion_clear H0.
 constructor.
 auto.
 intros.
 case ( In_merge_inv _ _ H1).
 simpl.
 destruct 1.
 subst y.
 auto with arith.
 apply le_trans with x1;auto.
 auto with arith.
 eapply sorted_inv_In.
 eauto.
 auto.
 simpl.
 intro;eapply sorted_inv_In.
 eauto.
 auto.
Qed.


Lemma flatten_sorted : forall t, sorted (flatten t).
Proof.
  intros t;functional induction (flatten t).
  (* first branch of flatten *)
  constructor.
  (* second branch of flatten *)
  constructor.
  (* third branch of flatten *)
  unfold merge;apply sorted_merge;simpl;assumption.
Qed.



(**********************
  This part shows that mergesort computes a permutation *)

Lemma how_many_insert : forall (t : tree bool (option nat)) n p, 
                    how_many_in_tree  p (insert _ n t) =
                    if eq_nat_dec p n 
                    then S (how_many_in_tree p t)
                    else how_many_in_tree p t.
Proof.
  intros t n;functional induction (insert _ n t);intro p.
  (* first branch of insert *)
  simpl;reflexivity.
  (* second branch of insert *)
  simpl.
  case (eq_nat_dec p n);case (eq_nat_dec p b);reflexivity.
  (* third branch of insert *)
  simpl. rewrite IHt0. case (eq_nat_dec p n);reflexivity.
  (* fourth branch of insert *)
  simpl. rewrite IHt0. case (eq_nat_dec p n);auto with arith.
Qed.

Lemma how_many_share : forall l n, how_many n l = how_many_in_tree n 
                                                  (share _ l).
Proof.
  intros l; functional induction (share _ l).
  simpl;reflexivity.
  simpl. 
  intro n;rewrite  how_many_insert.
 case (eq_nat_dec n a); auto.
Qed.


Lemma merge_plus : forall n ls, how_many n (pair_merge ls) =
                                   how_many n (fst ls) + how_many n (snd ls).
intros n ls.
functional induction (pair_merge ls).
simpl;auto.
 simpl;auto.
 simpl;auto.
 simpl in *.
 rewrite IHl.
 case (eq_nat_dec n x1).
 auto.
 auto.
 simpl. 
 case (eq_nat_dec n x2).
 rewrite IHl.
 intro ;subst x2.
 simpl.
 auto.
 intro; case (eq_nat_dec n x1).
 rewrite IHl.
 simpl;auto.
 intro;case (eq_nat_dec n x1).
 simpl;auto.
 intro d;case d;trivial.
 rewrite IHl;simpl.
 intro; case (eq_nat_dec n x1).
 intro;case n1;auto.
 auto.
Qed.


Lemma flatten_how_many : forall t  n, how_many n (flatten t)=
                                      how_many_in_tree n t.
Proof.
  intros t; functional induction (flatten t);intro m.
  
  simpl;reflexivity.

  simpl;reflexivity.

  unfold merge;rewrite merge_plus.
  rewrite IHl;rewrite IHl0;auto.
Qed.

Lemma merge_of_append : forall l l',
                        permutation (l++ l') (merge l l').
Proof.
 red.
 unfold merge. intros;rewrite  merge_plus.
 simpl.
 generalize l';induction l;simpl.
 auto.
 case (eq_nat_dec n a).
 intros;rewrite IHl.
 auto.
 auto.
Qed.

Lemma merge_and_sort : forall l l', sorted l -> sorted l' ->
                                    sort (l++l') (merge l l').
Proof.
 intros;red.
 split.
 unfold merge;apply sorted_merge;auto.
 apply merge_of_append.
Qed.

 


Theorem mergesort_permut : forall l , permutation l  (mergesort l).
Proof.
 intros;red;intros;unfold mergesort;rewrite (how_many_share l).
  rewrite flatten_how_many.
 auto.
Qed.


Theorem mergesort_ok : forall l, sort l (mergesort l).
Proof.
 intros;split.
 unfold mergesort; apply flatten_sorted.
 apply mergesort_permut.
Qed.


