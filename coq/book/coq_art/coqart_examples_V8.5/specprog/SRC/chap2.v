Require Export ZArith.
Require Export Arith.
Require Export Bool.

Open Scope Z_scope.
Check 100104.


Locate "_ * _".

Print Scope Z_scope.

Check 33%nat.

Check 0%nat.

Check O.


Open Scope nat_scope.

Check 33.

Check 0.

Check 33%Z.

Check (-12)%Z.


Open Scope Z_scope.

Check (-12).

Check (33%nat).


Check true.

Check false.


Check plus.

Check Zplus.


Check negb.

Check orb.

Check (negb true).

Check (negb (negb true)).

Check (((ifb (negb false)) true) false).

Open Scope nat_scope.

Check (S (S (S O))).

Check (mult (mult 5 (minus 5 4)) 7).

Check (5*(5-4)*7).


Check (S 3).

Check ((mult (mult (S (S (S (S (S O))))) 
                  (minus (S (S (S (S (S O)))))(S (S (S (S O))))))
            (S (S (S (S (S (S (S O))))))))).


Open Scope Z_scope.

Check (Zopp (Zmult 3 (Zminus (-5)(-8)))).


Check ((-4)*(7-7)).

Open Scope nat_scope.

Check (plus 3).

Check (Zmult (-5)).

Check Zabs_nat.

Check (5 + Zabs_nat (5-19)).

Check (fun n:nat => fun p:nat => fun z:Z => (Z_of_nat(n+p)+z)%Z).

Check (fun n p:nat => fun z:Z => (Z_of_nat(n+p)+z)%Z).

Check (fun (n p:nat)(z:Z) => (Z_of_nat(n+p)+z)%Z).

Check (fun a b c:Z => (b*b-4*a*c)%Z).

Check (fun (f g:nat->nat)(n:nat) => g (f n)).

Check (fun n (z:Z) f => (n+(Zabs_nat (f z)))%nat).

Check (fun n _:nat => n).

Check (fun n p:nat => p).

Check (fun n p : nat =>
   (let diff := n-p in
    let square := diff*diff in
        square * (square+n))%nat).

Definition t1 := 
 fun n:nat => let s := plus n (S n) in mult n (mult s s).

Check (fun i : nat =>
   let sum := plus i (S i) in mult i (mult sum sum)).

Check (fun n : nat =>
  let n := plus n (S n) in mult n (mult n n)).

Parameter max_int : Z.

Open Scope Z_scope.

Definition min_int := 1-max_int.

Print min_int.

Definition cube := fun z:Z => z*z*z. 
Reset cube.

Definition cube (z:Z) : Z := z*z*z.

Print cube.


Definition Z_thrice (f:Z->Z)(z:Z) := f (f (f z)).

Definition plus9 := Z_thrice (Z_thrice (fun z:Z => z+1)).

Section binomial_def.
 Variables a b:Z.
 
Definition binomial z:Z := a*z + b.
 
 Section trinomial_def.
  Variable c : Z.

  Definition trinomial z:Z := (binomial z)*z + c.
 
 End trinomial_def.

End binomial_def.

Print binomial.

Print trinomial.


Definition p1 : Z->Z := binomial 5 (-3).
Definition p2 : Z->Z := trinomial 1 0 (-1).
Definition p3  := trinomial 1 (-2) 1.

Section mab.
 Variables m a b:Z.
 Definition f := m*a*m.
 Definition g := m*(a+b).
End mab.
Print f.
Print g.

Section h_def.
 Variables a b:Z.
 Let s:Z := a+b.
 Let d:Z := a-b.
 Definition h : Z := s*s + d*d.
End h_def.

Print h.

Definition Zsqr (z:Z) : Z := z*z.


Definition my_fun (f:Z->Z)(z:Z) : Z := f (f z).

Eval cbv delta [my_fun Zsqr] in (my_fun Zsqr).

Eval cbv delta [my_fun] in (my_fun Zsqr).

Check ((fun (f:Z->Z)(z:Z) => f (f z))(fun (z:Z) => z*z)).

Check ( fun z:Z =>
        (fun z1:Z => z1*z1)((fun z0:Z => z0*z0) z)).

Check(  fun z:Z => (fun z1:Z => z1*z1)(z*z)).

Check ( fun z:Z => z*z*(z*z)).

Eval cbv beta delta [my_fun Zsqr] in (my_fun Zsqr).

Eval cbv  beta  delta [h] in (h 56 78).

Eval cbv  beta zeta delta [h] in (h 56 78). 

Eval compute in (h 56 78).

Eval compute in (my_fun Zsqr 3).


Check Z.

Check ((Z->Z)->nat->nat).

Check Set.

Check Type.

Definition Z_bin : Set := Z->Z->Z.

Check (fun z0 z1:Z => let d := z0-z1 in d*d).

Definition Zdist2 (z z0:Z) := let d := z-z0 in d*d.

Check (nat->nat).

Check (nat->nat:Type).

Section realization.
 Variables (A B :Set).
 Let spec : Set := (((A->B)->B)->B)->A->B.

 Let realization : spec 
       := fun (f:((A->B)->B)->B) a => f (fun g => g a).

End realization.

Definition nat_fun_to_Z_fun : Set := (nat->nat)->Z->Z.

Definition absolute_fun : nat_fun_to_Z_fun :=
  fun f z => Z_of_nat (f (Zabs_nat z)).

Definition always_0 : nat_fun_to_Z_fun :=
  fun _ _ => 0%Z.

Definition to_marignan : nat_fun_to_Z_fun :=
  fun _ _ => 1515%Z. 

Definition ignore_f : nat_fun_to_Z_fun :=
  fun _ z => z.

Definition from_marignan : nat_fun_to_Z_fun :=
  fun f _ => Z_of_nat (f 1515%nat).

Check and.

