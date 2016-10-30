Inductive triangular (A B : Type) :=
 base : B -> triangular A B
|constr : B -> triangular A (A * B) -> triangular A B. 

Check triangular_rec.

Definition m:triangular nat nat.
constructor 2.
exact 5.
constructor 1.
exact (1,1).
Defined.

Print m.

Fixpoint dim {A B : Type}(m : triangular A B) : nat :=
  match m with base _ _ _ => 1
             | constr _ _ _ m' => 1 + dim m'
  end.

Compute dim m.
Check m.


Require Import List.

Definition lower_row {A B : Type}(m : triangular A B): B * list A.
induction m.
exact (b, nil).
destruct IHm as [[x y] z].
exact (b,(x::z)).
Defined.

Fixpoint strip {A B : Type} (t : triangular A (A*B)): 
         (triangular A B) :=
 match t with base _ _ b => base _ _ (snd b)
            | constr _ _ b t' => constr _ _ (snd b) (strip t')
 end.



Compute lower_row m.


Fixpoint uniform {A B : Type}(a:A)(b:B)(n:nat) : triangular A B :=
  match n with 0 => base _ _ b
             | S p => constr _ _ b (uniform a (a,b)  p)
 end.



Fixpoint mystery {A B : Type}(f:A->A)(a:A)(b:B)(n:nat) : triangular A B :=
  match n with 0 => base _ _ b
             | S p => constr _ _ b (mystery f (f a) (f a, b)   p)
 end.



Definition ones (n:nat) := uniform 1 1 n.



Definition no_se (n:nat) := mystery S 1 1 n.


Compute lower_row (ones 10).

Fixpoint flatten {A}{B}(f: B -> list A) (m : triangular A B) : list A :=
 match m with base _ _ b => f b
            | constr  _ _ b m' => flatten (fun x=> fst x :: (f (snd x))) m' ++
                                 (f b)
 end.

Compute flatten (fun i => i::nil) (ones 3).

Compute flatten (fun i => i :: nil) (no_se 3).

Fixpoint aux (A B : Type) (a : A) (b : B) (n : nat) 
  (body : list (list A)) (d : list B) : list (A * B) :=
  match body, d, n with
   _, _, 0 => nil
  | l::tlb, v::tld, S p => (hd a l, v)::aux A B a b p tlb tld
  | nil, v::tld, S p => (a, v)::aux A B a b p nil tld
  | l::tlb, nil, S p => (hd a l, b)::aux A B a b p tlb nil
  | _, _, S p => (a, b)::aux A B a b p nil nil
  end.
   
Fixpoint mk_triangular (A B : Type) (a : A) (b : B)
   (d : list B) (body : list (list A)) (n : nat) : triangular A B :=
  match n with
    0 => base A B (nth 0 d b)
  | S p => constr A B (nth 0 d b)
              (mk_triangular A (A * B) a (a, b) 
                (aux A B a b (S p) body (tl d))
                (map (@tl _) body) p)
  end.

Compute (mk_triangular nat nat 0 0 (1::1::1::1::nil)
  ((2::3::4::nil)::(2::3::nil)::(2::nil)::nil) 3).

Compute flatten (fun i => i::nil) (mk_triangular nat nat 0 0 (1::1::1::1::nil)
  ((2::3::4::nil)::(2::3::nil)::(2::nil)::nil) 3).

Compute lower_row  (mk_triangular nat nat 0 0 (1::1::1::1::nil)
  ((2::3::4::nil)::(2::3::nil)::(2::nil)::nil) 3).
