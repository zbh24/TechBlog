(* Examples of type classes and Setoids *)
(* Version with operational classes *)
(* Some comments by Matthieu *)



Set Implicit Arguments.

Require Import ZArith.

Require Import Div2.

Require Import Recdef.

Open Scope Z_scope.

Class monoid_binop (A:Type) := monoid_op : A -> A -> A.
Infix "&" := monoid_op (at level 50, left associativity).

Class Monoid (A:Type)(dot : monoid_binop  A)(one : A) : Type := {
  dot_assoc : forall x y z:A, x & (y & z)=  x & y & z;
  one_left : forall x, one & x = x;
  one_right : forall x,  x & one = x}.

About one_right.
(*
one_right :
forall (A : Type) (dot : monoid_binop A) (one : A),
Monoid dot one -> forall x : A, x & one = x
*)



Require Import ZArith.
Open Scope Z_scope.

Print monoid_op.
Compute (@monoid_op _ Zmult 5 6).
Instance Zmult_op : monoid_binop Z := Zmult.
Compute 2 & 5.
Set Printing All.
Check 2 & 5.
Unset Printing All.


Instance ZMult : Monoid   Zmult_op  1.
split;intros; unfold Zmult_op, monoid_op; ring. 
Defined.

(* 2 x 2 Matrices *)

Class M2 : Set :={
  c00 : Z;  c01 : Z;
  c10 : Z;  c11 : Z}.

(* For using the notation (c00 m) *)
Implicit Arguments c00.
Implicit Arguments c01.
Implicit Arguments c10. 
Implicit Arguments c11.


Lemma M2_eq_intros :
  forall m m':M2, c00 m = c00 m' ->
                  c01 m = c01 m' ->
                  c10 m = c10 m' ->
                  c11 m = c11 m' -> m = m'.
destruct m;destruct m';simpl.
intros H H1 H2 H3;rewrite H ,H1, H2, H3;trivial.
Qed.


Instance Id2 : M2 := { c00 := 1;  c01 := 0;
                       c10 := 0;  c11 := 1}.

Instance M2_mult (m m':M2) : M2 :=
 Build_M2 
  (c00 m * c00 m' + c01 m * c10 m')  (c00 m * c01 m' + c01 m * c11 m')
  (c10 m * c00 m' + c11 m * c10 m')  (c10 m * c01 m' + c11 m * c11 m').

Instance M2_mult_op :  monoid_binop M2 := M2_mult.


Instance M2_Monoid : Monoid  M2_mult_op Id2. 
split.
destruct x;destruct y;destruct z;unfold monoid_op;simpl.
unfold M2_mult;apply M2_eq_intros;simpl; ring.
destruct x;simpl;unfold M2_mult_op, monoid_op;
unfold M2_mult; apply M2_eq_intros; lazy   [Id2 c00 c01 c10 c11];ring.
destruct x;simpl;unfold M2_mult_op, monoid_op;
unfold M2_mult;apply M2_eq_intros;lazy   [Id2 c00 c01 c10 c11];ring.
Defined.


Generalizable Variables A dot one.
About Monoid.


Fixpoint power `{M : @Monoid A dot one}(a:A)(n:nat) :=
  match n with 0%nat => one
             | S p => a & power a p
  end.


Infix "**" := power (at level 30, no associativity).
Compute  (2 ** 5) ** 2.
Set Printing Implicit.


Print power.
Unset Printing Implicit.

Compute (Build_M2 1 1  1 0) ** 40.



Section Z_additive.


Instance Z_plus_op :  monoid_binop Z:= Zplus.



Instance ZAdd : Monoid   Z_plus_op 0. 
split;intros;unfold Z_plus_op, monoid_op;ring.
Defined.

Compute 2 & 5.

Check  @monoid_op _ Zplus 2 5.
Check @monoid_op _ Zmult 2 5.

Compute 2 ** 5.
(* 32 *)

Compute power (M:=ZAdd) 2 5.
(* 10 *)

Set Printing Implicit.

Check (fun i:Z => (one_right i)).

Check (fun i:Z => one_right (Monoid:= ZMult) i).
(*
fun i : Z => @one_right Z Zmult 1 ZMult i
     : forall i : Z, i * 1 = i
*)
Unset Printing Implicit.

(* OK, let's remove ZAdd *)
End Z_additive.


(* A tail recursive linear function *)
Fixpoint power_mult `{M : Monoid }
     (acc x:A)(n:nat) : A (*  acc & (x ** n) *) :=
  match n with 0%nat => acc
             | S p => power_mult (acc & x) x p
  end.

Definition tail_recursive_power  `{M : Monoid}(x:A)(n:nat) :=
     power_mult one x n.

Require Import Recdef.
Require Import Div2.

(* rejected by The syntax analyser 
Function binary_power_mult `{M: @Monoid A dot one} 
      (acc x:A)(n:nat){measure (fun i=>i) n} : A 


Ok, too bad ... *)

Function binary_power_mult (A:Type)(dot:monoid_binop A)(one:A) 
    (M: @Monoid A dot one) (acc x:A)(n:nat){measure (fun i=>i) n} : A 
  (* acc & (x ** n) *) :=
  match n with 0%nat => acc
             | _ => match Even.even_odd_dec n
                    with left H0 => binary_power_mult    _   acc (dot x x) (div2 n)
                       | right H1 => 
                         binary_power_mult   _  (acc & x) ( x & x) (div2 n)
                    end
  end.
intros;apply lt_div2; auto with arith.
intros;apply lt_div2; auto with arith.
Defined.
About Monoid.


Definition binary_power `{M: Monoid} (x:A)(n:nat)  := 
     binary_power_mult    M one  x n.

Compute binary_power  2 5.

Compute power  (Build_M2 1 1 1 0) 10.

Compute binary_power (Build_M2 1 1 1 0) 20.



Section About_power.

  Context      `(M:Monoid  ).

  
  Ltac monoid_rw :=
    rewrite one_left || rewrite one_right || rewrite dot_assoc.

  Ltac monoid_simpl := repeat monoid_rw.

  Lemma power_x_plus : forall x n p, x ** (n + p) = x ** n & x ** p.
  Proof.
   induction n;simpl. 
     intros; monoid_simpl;trivial.
    intro p;rewrite (IHn p); monoid_simpl;trivial.
  Qed.

  Ltac power_simpl := repeat (monoid_rw || rewrite <- power_x_plus).

  Lemma power_commute : forall x n p,  
               x ** n & x ** p = x ** p & x ** n. 
  Proof.
   intros x n p;power_simpl;  rewrite (plus_comm n p);trivial.
 Qed.

 Lemma power_commute_with_x : forall x n ,  
        x & x ** n = x ** n & x.
                                
 Proof.
  induction n;simpl;power_simpl;trivial.
  repeat rewrite <- dot_assoc; rewrite IHn; trivial.
 Qed.

 Lemma power_of_power : forall x n p,  (x ** n) ** p = x ** (p * n).
 Proof.
   induction p;simpl;[| rewrite power_x_plus; rewrite IHp]; trivial.
Qed.


Lemma power_S : forall x n, x &  x ** n = x ** S n.
Proof. intros;simpl;auto. Qed.

Lemma sqr : forall x, x ** 2 =  x & x.
Proof.
 simpl;intros;monoid_simpl;trivial.
Qed.

Ltac factorize := repeat (
                rewrite <- power_commute_with_x ||
                rewrite  <- power_x_plus  ||
                rewrite <- sqr ||
                rewrite power_S ||
                rewrite power_of_power).

 Lemma power_of_square : forall x n, (x & x) ** n = x ** n & x ** n.
  induction n;simpl;monoid_simpl;trivial.
  repeat rewrite dot_assoc;rewrite IHn; repeat rewrite dot_assoc.
 factorize; simpl;trivial.
 Qed.

 Lemma power_mult_correct : 
    forall n x, tail_recursive_power x n = x ** n.
  Proof.
    intros n x;  unfold tail_recursive_power.
    rewrite <-  (one_left  (power x n)).
    assert (forall y:A, power_mult y x n =  y & (power x n));auto.
       generalize n x;intro p; induction p;simpl;intros; monoid_simpl;auto.
  Qed.

Lemma binary_power_mult_ok :
  forall n a x,  binary_power_mult  M a x n = a & x ** n.
Proof.
  intro n; pattern n;apply lt_wf_ind.
  clear n; intros n Hn;   destruct n.
   intros;simpl; rewrite binary_power_mult_equation;monoid_simpl;
    trivial.
  intros;  
    rewrite binary_power_mult_equation; destruct (Even.even_odd_dec (S n)).
  rewrite Hn.  rewrite power_of_square;  factorize.
 pattern (S n) at 3;replace (S n) with (div2 (S n) + div2 (S n))%nat;auto.
 generalize (even_double _ e);simpl;auto. 
  apply lt_div2;auto with arith.
  rewrite Hn. 
 rewrite power_of_square ; factorize.
pattern (S n) at 3;replace (S n) with (S (div2 (S n) + div2 (S n)))%nat;auto.

rewrite <- dot_assoc; factorize;auto.
generalize (odd_double _ o);intro H;auto.
apply lt_div2;auto with arith.
Qed.

Lemma binary_power_ok : forall x n, binary_power (x:A)(n:nat) = x ** n.
Proof.
  intros n x;unfold binary_power;rewrite binary_power_mult_ok;
  monoid_simpl;auto.
Qed.

End About_power.

Definition fibonacci (n:nat) :=
      c00 (binary_power (Build_M2 1 1 1 0) n).

Compute fibonacci 20. 


Class Abelian_Monoid `(M:Monoid ):= {
  dot_comm : forall x y, x & y = y & x}.

Instance ZMult_Abelian : Abelian_Monoid ZMult.
split. 
 exact Zmult_comm.
Defined.

Section problem.

(* I don't understand why it fails ???? *)

Class Abelian_Monoid' (A:Type)(dot : monoid_binop  A)(one : A) : Type := {
  the_monoid :> Monoid dot one;
   dot_comm' : forall x y, x & y = y & x}.


Program Instance AM' : Abelian_Monoid' Zmult 1.
Next Obligation.
unfold Z_plus_op, monoid_op;ring.
Defined.
Print AM'.

(*

The following commands fail !
Check (dot_assoc (M:=AM')).

Because the_monnoid is not a coercion, just a projection that is 
used during resolution! If one asks for a Monoid instance and
only an Abelian_Monoid' is available, the projection [the_monoid]
is used.

*) 

Context d `{Abelian_Monoid' nat d}.

Check power (A:=nat).

Check (_:Monoid  Zmult 1).

Check (power (M:=the_monoid (A:=Z))).

End problem.


Section Power_of_dot.
 Context (A:Type)`(M: Monoid A)(AM:Abelian_Monoid M).
 
Theorem power_of_mult :
   forall n x y, (x & y) ** n =  x ** n  & y ** n. 
Proof.
 induction n;simpl.
 rewrite one_left;auto.
 intros; rewrite IHn; repeat rewrite dot_assoc.
  rewrite <- (dot_assoc  x y (power x n)); rewrite (dot_comm y (power x n)).
 repeat rewrite dot_assoc;trivial.
Qed.

End Power_of_dot.

Goal forall (x y z :Z)(n:nat),  (x & (y & z)) ** n  =
                        x ** n &  (y ** n  & z ** n).
intros.
repeat (rewrite power_of_mult); trivial. 
apply ZMult_Abelian.
apply ZMult_Abelian.
Qed.


(*** Monoids with equivalence *)


Require Import  Setoid.

Require Import Morphisms.

Class Equiv A := equiv : relation A.
Infix "==" := equiv (at level 70):type_scope.


 


(* Exercise :
   
   Define  the monoid of binary relations over some type A 
   is it abelian ?
   Solution booksite_trunk/newstuff/CVS_ONLY/monoids_exo.v 
*)


