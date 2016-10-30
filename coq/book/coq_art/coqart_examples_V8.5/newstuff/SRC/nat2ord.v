Inductive Ord : Set :=
|  zero : Ord
|  succ : Ord -> Ord
| limit : (nat->Ord)->Ord.


Fixpoint nat2ord (n:nat) : Ord :=
 match n with 0 => zero
            | S p => succ (nat2ord p)
 end.


Fixpoint plus (o1 o2:Ord){struct o2} :=
  match o2 with zero => o1
              | succ o2' => succ (plus o1  o2')
              | limit f => limit (fun n => plus o1 (f n))
  end.
Notation  "o1 + o2" := (plus o1 o2):o_scope.
Open Scope o_scope.

Coercion nat2ord : nat >-> Ord.

Definition omega := limit (fun n => n).


Check (succ 23).
Check (omega = 2+omega).

Check (succ (3+5)).

Eval compute in (succ (3+5)).

