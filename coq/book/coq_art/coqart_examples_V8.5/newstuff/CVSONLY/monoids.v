(* Examples of type classes and Setoids *)


Set Implicit Arguments.

Require Import ZArith.

Require Import Div2.

Require Import Recdef.

Open Scope Z_scope.

Fixpoint power (a:Z)(n:nat) :=
  match n with 0%nat => 1
             | S p =>  a * power a p
  end.

Eval vm_compute in power 2 40.

Definition tail_recursive_power (a:Z)(n:nat) :=
 let fix power_mult (acc : Z)(n:nat): Z := (* acc *a ^ n *)
     match n with 0%nat => acc
             | S p => power_mult (acc * a) p
  end
 in power_mult  1 n.

Eval vm_compute in tail_recursive_power 2 40.


Function binary_power_mult  (acc x:Z)(n:nat){measure (fun i=>i) n} : Z
  (* acc * (power x n) *) :=
  match n with 0%nat => acc
             | _ => if Even.even_odd_dec n
                    then binary_power_mult  acc (x * x) (div2 n)
                    else  binary_power_mult  (acc * x) (x * x) (div2 n)
                    end.
intros;apply lt_div2; auto with arith.
intros;apply lt_div2; auto with arith.
Defined.


Definition binary_power (x:Z)(n:nat) := binary_power_mult 1 x n.

Eval vm_compute in binary_power 2 40.

Goal binary_power 2 234 = power 2 234.
reflexivity.
Qed.

(*
Definition morphism (m m':Monoid)(phi: domain m -> domain m') :=
   phi (one m)= one m' /\
   forall x y: domain m, phi (dot m x y) = dot m' (phi x) (phi y).


Goal morphism ZMult M2_Monoid (fun k => {| c00 := k;  c01 := 0;
                       c10 := 0;  c11 := k|}) .
split.
simpl. trivial.
intros x y;simpl. unfold M2_mult. apply M2_eq_intros;simpl; ring.
Qed.

Record Commutative_Monoid : Type:= mk_comm_monoid {
  comm_mono :> Monoid;
  comm_comm : forall x y:(domain comm_mono), dot  comm_mono x y =
                                             dot  comm_mono y x
}.

Require Import JMeq.
Definition Monoid_equiv (M M':Monoid) :=
  domain M = domain M' /\
  JMeq (one M) = JMeq (one M') /\
  forall x y x' y' , JMeq x y -> JMeq x' y' -> JMeq (dot M x y) (dot M x' y').



Check Commutative_Monoid_ind.

Check (fun c : Commutative_Monoid => dot c).

*)
 
Reset power.

(* trouver un vrai inconvenient de cette representation *)

Class Monoid {A:Type}(dot : A -> A -> A)(one : A) : Type := {
  dot_assoc : forall x y z:A, dot x (dot y z)= dot (dot x y) z;
  one_left : forall x, dot one x = x;
  one_right : forall x, dot x one = x}.

Print Monoid.


(*



Record Monoid (A : Type) (dot : A -> A -> A) (one : A) : Type := Build_Monoid
  { dot_assoc : forall x y z : A, dot x (dot y z) = dot (dot x y) z;
    one_left : forall x : A, dot one x = x;
    one_right : forall x : A, dot x one = x }

For Monoid: Argument A is implicit
For Build_Monoid: Argument A is implicit
For Monoid: Argument scopes are [type_scope _ _]
For Build_Monoid: Argument scopes are [type_scope _ _ _ _ _]
*)

About one_right.

(*
one_right :
forall (A : Type) (dot : A -> A -> A) (one : A),
Monoid dot one -> forall x : A, dot x one = x

Arguments A, dot, one, Monoid are implicit and maximally inserted
Argument scopes are [type_scope _ _ _ _]
one_right is transparent
Expands to: Constant Top.one_right
*)

(* First example : (Z,*,1) *)

Require Import ZArith.
Open Scope Z_scope.

Instance ZMult : Monoid  Zmult 1.
split.

intros;ring.
intros;ring.
intros;ring.
Qed.

About one_left.


Goal forall n:Z, 1 * (n * 1) = n.
intro n;rewrite one_left;rewrite one_right;trivial.
Save XX.

Generalizable Variables A dot one.
Section power_def.

Fixpoint power `{M: Monoid A dot one}(a:A)(n:nat) :=
  match n with 0%nat => one
             | S p => dot a (power a p)
  end.

Function binary_power_mult A dot one (M: @Monoid A dot one)
     (acc x:A)(n:nat){measure (fun i=>i) n} : A 
  (* acc * (x ** n) *) :=
  match n with 0%nat => acc
             | _ => match Even.even_odd_dec n
                    with left H0 => binary_power_mult  _   acc (dot x x) (div2 n)
                       | right H1 => 
                         binary_power_mult   _ (dot acc  x) (dot  x  x) (div2 n)
                    end
  end.
intros;apply lt_div2; auto with arith.
intros; apply lt_div2; auto with arith.
Defined.


Definition binary_power `{M:Monoid} x n := binary_power_mult M one x n.

End power_def.
Ltac monoid_rw :=
    rewrite one_left || rewrite one_right || rewrite dot_assoc.



(* 2 x 2 Matrices *)

Require Import Ring.

Section matrices.
 Variables (A:Type)
           (zero one : A) 
           (plus mult minus : A -> A -> A)
           (sym : A -> A).
 Notation "0" := zero.  Notation "1" := one.
 Notation "x + y" := (plus x y).  
 Notation "x * y " := (mult x y).
 


 Variable rt : ring_theory  zero one plus mult minus sym (@eq A).

 Add  Ring Aring : rt.

 Structure M2 : Type := {c00 : A;  c01 : A;
                         c10 : A;  c11 : A}.


Lemma M2_eq_intros :
  forall m m':M2, c00 m = c00 m' ->
                  c01 m = c01 m' ->
                  c10 m = c10 m' ->
                  c11 m = c11 m' -> m = m'.
destruct m;destruct m';simpl.
intros H H1 H2 H3;rewrite H ,H1, H2, H3;trivial.
Qed.


Definition Id2 : M2 := Build_M2  1 0 0 1.

Definition M2_mult (m m':M2) : M2 :=
 Build_M2 (c00 m * c00 m' + c01 m * c10 m')
          (c00 m * c01 m' + c01 m * c11 m')
          (c10 m * c00 m' + c11 m * c10 m')
          (c10 m *  c01 m' +  c11 m * c11 m').




Global Instance M2_Monoid : Monoid  M2_mult Id2. 
split.
destruct x;destruct y;destruct z;simpl.
unfold M2_mult;apply M2_eq_intros;simpl;  ring.
destruct x;simpl;
unfold M2_mult; apply M2_eq_intros; lazy   [Id2 c00 c01 c10 c11];ring.
destruct x;simpl;
unfold M2_mult;apply M2_eq_intros;lazy   [Id2 c00 c01 c10 c11];ring.
Defined.

End matrices.

Instance M2Z : Monoid  _ _ := M2_Monoid Zth.


About power.


Compute power (Build_M2 1 1 1 0) 40.



Definition fibonacci (n:nat) :=
  c00 (power  (Build_M2 1 1 1 0) n).

Compute  fibonacci 20.


About power.

Section About_power.

Require Import Arith.
 Context      `(M:Monoid A dot one ).


  Ltac monoid_simpl := repeat monoid_rw.

  Local Infix "*" := dot.
  Local Infix "**" := power (at level 30, no associativity).


  Lemma power_x_plus : forall x n p, x ** (n + p) =  x ** n *  x ** p.
  Proof.
   induction n;simpl. 
     intros; monoid_simpl;trivial.
    intro p;rewrite (IHn p); monoid_simpl;trivial.
  Qed.

  Ltac power_simpl := repeat (monoid_rw || rewrite <- power_x_plus).

  Lemma power_commute : forall x n p,  
               x ** n * x ** p = x ** p * x ** n. 
  Proof.
   intros x n p;power_simpl;  rewrite (plus_comm n p);trivial.
 Qed.

 Lemma power_commute_with_x : forall x n ,  
        x * x ** n = x ** n * x.
                                
 Proof.
  induction n;simpl;power_simpl;trivial.
  repeat rewrite <- dot_assoc; rewrite IHn; trivial.
 Qed.

 Lemma power_of_power : forall x n p,  (x ** n) ** p = x ** (p * n).
 Proof.
   induction p;simpl;[| rewrite power_x_plus; rewrite IHp]; trivial.
Qed.


Lemma power_S : forall x n, x *  x ** n = x ** S n.
Proof. intros;simpl;auto. Qed.

Lemma sqr : forall x, x ** 2 =  x * x.
Proof.
 simpl;intros;monoid_simpl;trivial.
Qed.

Ltac factorize := repeat (
                rewrite <- power_commute_with_x ||
                rewrite  <- power_x_plus  ||
                rewrite <- sqr ||
                rewrite power_S ||
                rewrite power_of_power).

 Lemma power_of_square : forall x n, (x * x) ** n = x ** n * x ** n.
  induction n;simpl;monoid_simpl;trivial.
  repeat rewrite dot_assoc;rewrite IHn; repeat rewrite dot_assoc.
 factorize; simpl;trivial.
 Qed.

 
Lemma binary_power_mult_ok :
  forall n a x,  binary_power_mult  M  a x n = a * x ** n.
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


About binary_power_ok.

Implicit Arguments binary_power_ok [A dot one M].
About binary_power.
(*

binary_power_ok :
forall (A : Type) (dot : A -> A -> A) (one : A) (M : @Monoid A dot one)
  (x : A) (n : nat),
@binary_power A dot one (x:A) (n:nat) = @power A dot one M x n

Arguments A, dot, one are implicit and maximally inserted
Argument scopes are [type_scope _ _ _ _ nat_scope]
binary_power_ok is opaque
Expands to: Constant Top.binary_power_ok

*)

Check binary_power_ok (Build_M2 1 1 1 0) 40.

Eval vm_compute in power 2 5.


About power.








