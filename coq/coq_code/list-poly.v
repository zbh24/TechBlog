Require Export String.
Open Scope string_scope.


Inductive natlist : Type :=
  | nil : natlist
  | cons : nat-> natlist->natlist.

Inductive boollist:Type :=
  | bnil:boollist
  | bcons:bool->boollist->boollist.

Check (cons 1 (cons 2 nil)).

Notation "x :: l" := (cons x l).

Check (3::nil).
Notation "[]" := nil.

Fixpoint repeat(x : nat) (count : nat) : natlist :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat x count')
  end.
(* First method:poly_start*)
Inductive list (X:Type) :=
  | poly_nil :list X
  | poly_cons : X->list X -> list X.

Print list.

Check (poly_nil nat).

Check (cons 1 (cons 2 nil)).
Check (poly_cons nat 1 (poly_cons nat 2 (poly_nil nat))).
(* It is wrong *)
(* Check (poly_cons 1 (poly_cons 2 poly_nil)).  *)

Fixpoint poly_repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => poly_nil X
  | S count' => poly_cons X x (poly_repeat X x count')
  end.

Arguments poly_nil {X}.
Arguments poly_cons {X} _ _.
Arguments poly_repeat {X} x count.

Check (poly_cons true poly_nil).
(* First method:poly_end*)

(* Second method:poly_start*)
Fixpoint poly_repeat' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => poly_nil
  | S count' => poly_cons x (poly_repeat x count')
  end.

(* Don't recommend this style of definition *)
Inductive list' {X:Type} : Type :=
  | nil' : list'
  | cons' : X -> list'->list'.

Check (cons' 4 nil').

Fixpoint app {X : Type} (l1 l2 : list X)
             : list X :=
  match l1 with
  | poly_nil => l2
  | poly_cons h t => poly_cons h (app t l2)
  end.

(* Fixpoint app' (l1 l2: list') :list':= *)
(*   match l1 with *)
(*   | nil' => l2 *)
(*   | cons' h t => cons' h (app' t l2) *)
(*   end. *)


  
(* Second  method:poly_end*)

(* Most achieved write style *)

Inductive list1 (X:Type) :=
  | poly_nil1 :list1 X
  | poly_cons1 : X->list1 X -> list1 X.

Arguments poly_nil1 {X}.
Arguments poly_cons1 {X} _ _.

Check list1 nat.

Fixpoint app1 {X : Type} (l1 l2 : list1 X)
             : list1 X:=
  match l1 with
  | poly_nil1 => l2
  | poly_cons1 h t => poly_cons1 h (app1  t l2)
  end.


Inductive result (X: Set) : Set :=
  | Error (err: list string) : result X
  | Ok :X-> result X.

Arguments Ok {X} _.
Arguments Error {X} _.

Inductive result1 (X: Set) : Set :=
  | Error1 (err: list string) : result1 X
  | Ok1 (a: X) : result1 X.

Implicit Arguments Error1 [X]. 
Implicit Arguments Ok1 [X]. 

Check (Error1 (poly_cons "there is no one" poly_nil)).
Check (Ok 3).

Notation "'do' x <-- A ; B " := 
  (match A with 
     | Some y => (fun x => B) y 
     | None => Error (poly_cons "Unknown Error" poly_nil)
   end)
 (at level 200, x ident).

Notation "'ret' x" := (Ok x) (at level 200, only parsing).

Definition zbh (a:option nat) : result nat :=
  ret 3
.

(*** IMPORTANT ***)
(* recommand the inductive style and definition style *)
Inductive list1' (X:Type) :=
  | poly_nil1' :list1' X
  | poly_cons1' : X->list1' X -> list1' X.

Arguments poly_nil1' {X}.
Arguments poly_cons1' {X} _ _.

Fixpoint app1' {X : Type} (l1 l2 : list1' X)
             : list1' X:=
  match l1 with
  | poly_nil1' => l2
  | poly_cons1' h t => poly_cons1' h (app1'  t l2)
  end.

