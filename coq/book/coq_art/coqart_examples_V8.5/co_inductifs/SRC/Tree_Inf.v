Require Export Ltree.
Require Export building.
Require Export graft_unfold.

Set Implicit Arguments.

(*  having some infinite branch *)

CoInductive SomeInf (A:Set):(LTree A)->Prop :=
   InfLeft : forall (a:A)(t1 t2:LTree A),
                                    SomeInf t1 ->
                                    SomeInf (LBin a t1 t2)
|  InfRight : forall (a:A)(t1 t2:LTree A),
                                     SomeInf t2 ->
                                     SomeInf (LBin a t1 t2).

(*  every branch is infinite *)
CoInductive EveryInf (A:Set) :(LTree A)->Prop :=
  InfI : forall (a:A) (t1 t2: LTree A),
                                EveryInf t1 ->
                                EveryInf t2 ->
                                EveryInf (LBin a t1 t2).


(* having some finite branch *)

Inductive SomeFin (A:Set) : (LTree A)->Prop :=
  SomeFin_leaf : SomeFin LLeaf
| SomeFin_left : forall (a:A) (t1 t2: LTree A),
                                      SomeFin t1 ->
                                      SomeFin (LBin a t1 t2)
| SomeFin_right : forall (a:A) (t1 t2: LTree A),
                                      SomeFin t2 ->
                                      SomeFin (LBin a t1 t2).

(* Every branch is finite (i.e. this is a finite tree) *)


Inductive Finite (A:Set) :(LTree A)->Prop :=
  Finite_leaf : Finite LLeaf 
| Finite_bin : forall (a:A) (t1 t2: LTree A),
                                      Finite t1 ->
                                      Finite t2 ->
                                      Finite (LBin a t1 t2).

Hint Resolve Finite_leaf Finite_bin SomeFin_leaf 
SomeFin_left  SomeFin_right.

(*

  Some examples :

*)


(* we prove that the tree built in module building has 
   only infinite branches *)

(* technical unfolding lemma *)

Lemma postree_unfold : forall p, PosTree p =
                                LBin p (PosTree (xO p)) (PosTree (xI p)).
Proof.
  intros p; LTree_unfold (PosTree p).
  simpl.
  trivial.
Qed.  


Lemma postree_inf : forall p, EveryInf  (PosTree  p).
Proof.
 cofix.
 intro p.
 rewrite (postree_unfold p); split; auto.
Qed.

(* a tree with an infinite branch *)

CoFixpoint zigzag (b:bool): LTree bool :=
    if b then (LBin b LLeaf (zigzag false))
         else (LBin b (zigzag true) LLeaf ).
           
(*
       true
      /   \
    Leaf  false
          /   \
       true    Leaf
      /   \
    Leaf  false
          /   \
       true    Leaf
      /   \
    Leaf  false
          /   \
       true    Leaf
       ...
*)



Lemma zigzag_unfold : forall b,
                        zigzag b =
                        if b
                        then LBin b LLeaf (zigzag false)
                        else LBin b (zigzag true) LLeaf.
Proof.
 intro b;LTree_unfold (zigzag b).
 simpl.
 case b; simpl; auto.
Qed.

Lemma zigzag_inf : forall b, SomeInf (zigzag b).
Proof.
  cofix.
  intro b;
   rewrite (zigzag_unfold b).
  case b; simpl ;[right|left]; auto.
Qed.


(* Some Finite/Infinite relationships *)


Lemma Finite_Not_SomeInf : forall (A:Set) (t: LTree A),
                              Finite t -> ~ SomeInf t.
Proof.
 intros A t H; elim H.
 red; inversion 1.
 red; intros a t1 t2 Ht1 H't1 Ht2 H't2 H'.
 inversion H'; tauto.
Qed.


Lemma SomeInf_Not_Finite : forall (A:Set) (t: LTree A),
                             SomeInf t -> ~ Finite t.
Proof.
 intros A t.
 generalize (Finite_Not_SomeInf (t:=t)); tauto.
Qed.


Lemma SomeFin_Not_EveryInf : forall (A:Set)(t: LTree A),
                              SomeFin t -> ~ EveryInf t.
Proof.
  intros A t Ht; induction Ht;
   red; inversion 1; auto.
Qed.

Lemma Not_SomeFin_EveryInf : forall (A:Set)(t: LTree A),
                              ~ SomeFin t -> EveryInf t.
Proof.
 intros A ; cofix.  
 intro t; case t.
 destruct 1; auto.
 intros a t1 t2 H; split ;
  apply Not_SomeFin_EveryInf ;
  red; intro; apply H ;auto.
Qed.


Section classic.
  Hypothesis class:forall P:Prop, ~~P ->P.


  Remark demorgan : forall P Q, ~(~P /\ ~Q)-> P \/ Q.
  Proof.  
    intros;
    apply class; tauto.
  Qed.

  Remark  Not_Finite_or : forall (A:Set) (a:A) (t1 t2: LTree A),
                          ~ Finite (LBin a t1 t2) ->
                          ~ Finite t1  \/  ~Finite t2.
  Proof.
   intros A a t1 t2 H.
   apply demorgan.
   intro; apply H.
   right; apply class; tauto.
  Qed.

  Lemma Not_Finite_SomeInf : forall (A:Set)(t: LTree A),
                               ~Finite t -> SomeInf t.
  Proof.
   intro A; cofix the_thm.
   intro t ;case t.
   intro H; case H; left.
   intros a0 t1 t2 H.
   case (Not_Finite_or H);
     [left|right];
      apply the_thm ; auto.
   Qed.
    
End classic.

Theorem graft_Finite_LLeaf : forall (A:Set) (t: LTree A),
                             Finite t ->
                             graft t LLeaf = t.
Proof.
 intros A t H; induction H.
 rewrite graft_unfold; auto.
 rewrite graft_unfold.
 rewrite IHFinite1; rewrite IHFinite2; auto.
Qed.

